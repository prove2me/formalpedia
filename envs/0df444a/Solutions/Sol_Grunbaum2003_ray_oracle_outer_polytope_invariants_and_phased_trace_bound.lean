-- Prove2me | solution 1 for Grunbaum2003.ray_oracle_outer_polytope_invariants_and_phased_trace_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T22:49:48.478138+00:00
-- url     : https://prove2.me/submissions/1fc709dc-5a29-4986-8f9a-6ac1192f782a

import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Theorems.Thm_Grunbaum2003_rayOracle_local_sector_and_known_facet_exclusion
import Theorems.Thm_Grunbaum2003_repaired_ray_query_budget_bound
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Theorems.Thm_Grunbaum2003_polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
open Classical

namespace Grunbaum2003

/-- Outer halfspace approximation defined by a subset `S` of facet indices. -/
def outerHalfspacePolytope {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (S : Finset (Fin m)) : Set (Fin d → ℝ) :=
  {x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}

lemma subset_outerHalfspacePolytope {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1})
    (S : Finset (Fin m)) :
    P ⊆ outerHalfspacePolytope L S := by
  intro x hx i hi
  rw [hP] at hx
  exact hx i

lemma outerHalfspacePolytope_antitone {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {S S' : Finset (Fin m)} (hSS' : S ⊆ S') :
    outerHalfspacePolytope L S' ⊆ outerHalfspacePolytope L S := by
  intro x hx i hi
  exact hx i (hSS' hi)

lemma certified_extremePoints_persist {d : ℕ} {P Q Q' : Set (Fin d → ℝ)}
    (hPQ' : P ⊆ Q') (hQ'Q : Q' ⊆ Q) :
    P ∩ Q.extremePoints ℝ ⊆ P ∩ Q'.extremePoints ℝ ∧
    P ∩ Q'.extremePoints ℝ ⊆ P.extremePoints ℝ := by
  refine ⟨?_, inter_extremePoints_subset_extremePoints_of_subset hPQ'⟩
  intro x ⟨hxP, hxQ⟩
  exact ⟨hxP, inter_extremePoints_subset_extremePoints_of_subset hQ'Q ⟨hPQ' hxP, hxQ⟩⟩

lemma fresh_facet_of_failed_extreme_verification {d m : ℕ} (hd : 0 < d)
    {P : Set (Fin d → ℝ)} (hConv : Convex ℝ P) (hClosed : IsClosed P)
    (h0 : (0 : Fin d → ℝ) ∈ interior P)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (hP : P = {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)} (hOracle : IsPolytopeRayOracle P oracle)
    (S : Finset (Fin m)) {v : Fin d → ℝ}
    (hv : v ∈ (outerHalfspacePolytope L S).extremePoints ℝ)
    (hne : oracle v ≠ v) {i_new : Fin m} (hi_new : L i_new (oracle v) = 1) :
    i_new ∉ S ∧ (insert i_new S).card = S.card + 1 := by
  have hPQ : P ⊆ outerHalfspacePolytope L S := subset_outerHalfspacePolytope L hP S
  let k := S.card
  let e : Fin k ≃ S := (Finset.equivFin S).symm
  let L_S : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ := fun j => (L (e j).val).toLinearMap
  have hv_le : ∀ j : Fin k, L_S j v ≤ 1 := by
    intro j
    exact hv.1 (e j).val (e j).property
  have hexcl := (rayOracle_local_sector_and_known_facet_exclusion.{0}.2.1
    hd hConv hClosed h0 hPQ hOracle hv hne L_S hv_le).2
  have hnot_mem : i_new ∉ S := by
    intro hmem
    let j : Fin k := e.symm ⟨i_new, hmem⟩
    have hj : (e j).val = i_new := by
      simp [j]
    have hlt : L (e j).val (oracle v) < 1 := hexcl j
    rw [hj, hi_new] at hlt
    exact lt_irrefl 1 hlt
  exact ⟨hnot_mem, Finset.card_insert_of_notMem hnot_mem⟩

lemma outer_polytope_and_certified_vertices_eq_of_all_verified {d : ℕ}
    {P Q V_Q C : Set (Fin d → ℝ)}
    (hConv : Convex ℝ P) (hPQ : P ⊆ Q) (hQ : Q = convexHull ℝ V_Q)
    (hVQ_C : V_Q ⊆ C) (hC_extP : C ⊆ P.extremePoints ℝ)
    (hExtQ_C : Q.extremePoints ℝ ⊆ C) :
    Q = P ∧ C = P.extremePoints ℝ := by
  have hC_P : C ⊆ P := fun x hx => (hC_extP hx).1
  have hQP : Q ⊆ P := by
    rw [hQ]
    exact convexHull_min (hVQ_C.trans hC_P) hConv
  have hQP_eq : Q = P := Set.Subset.antisymm hQP hPQ
  refine ⟨hQP_eq, Set.Subset.antisymm hC_extP ?_⟩
  rw [← hQP_eq]
  exact hExtQ_C

lemma extremePoints_eq_exposed_singletons_of_isDPolytope {d : ℕ} {P : Set (Fin d → ℝ)}
    (hP : IsDPolytope P) :
    P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} ∧
    faceCount P 0 = (P.extremePoints ℝ).ncard := by
  have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices d P hP
  have hVBound := Grunbaum2003.polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound d P
  let V_set : Set (Fin d → ℝ) := {x : Fin d → ℝ | IsExposed ℝ P {x}}
  have hP_eq_V : P = convexHull ℝ V_set := by
    have h1 := hHull.2 ⟨P, IsExposed.refl P⟩
    change P = convexHull ℝ (P ∩ V_set) at h1
    have hsub : V_set ⊆ P := fun x hx => hx.subset (Set.mem_singleton x)
    rw [Set.inter_eq_self_of_subset_right hsub] at h1
    exact h1
  have heq : P.extremePoints ℝ = V_set := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [hP_eq_V] at hx
      exact extremePoints_convexHull_subset hx
    · intro v hv
      obtain ⟨l, hvl⟩ := hv (Set.singleton_nonempty v)
      have hv_mem : v ∈ {z ∈ P | ∀ w ∈ P, l w ≤ l z} := by
        rw [← hvl]; exact Set.mem_singleton v
      rw [mem_extremePoints_iff_left]
      refine ⟨hv_mem.1, fun x hx y hy hseg => ?_⟩
      rcases hseg with ⟨a, b, ha, hb, hab, hcomb⟩
      have hlx : l x ≤ l v := hv_mem.2 x hx
      have hly : l y ≤ l v := hv_mem.2 y hy
      have hcomb_l : a * l x + b * l y = l v := by
        calc a * l x + b * l y
            = l (a • x + b • y) := by rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
          _ = l v := by rw [hcomb]
      have hsum_zero : a * (l v - l x) + b * (l v - l y) = 0 := by
        calc a * (l v - l x) + b * (l v - l y)
            = (a + b) * l v - (a * l x + b * l y) := by ring
          _ = 1 * l v - l v := by rw [hab, hcomb_l]
          _ = 0 := by ring
      have hlx_eq : l x = l v := by nlinarith
      have hx_in : x ∈ ({v} : Set (Fin d → ℝ)) := by
        rw [hvl]
        exact ⟨hx, fun w hw => by linarith [hv_mem.2 w hw]⟩
      exact Set.mem_singleton_iff.1 hx_in
  refine ⟨heq, ?_⟩
  rw [heq, hVBound.1]

lemma face_subset_hyperplane_iff_exposed_vertices_eq_one {d : ℕ} {P : Set (Fin d → ℝ)}
    (hP : IsDPolytope P) (F : PolytopeFace P) (l : (Fin d → ℝ) →L[ℝ] ℝ) :
    F.val ⊆ {x : Fin d → ℝ | l x = 1} ↔
      ∀ v : Fin d → ℝ, IsExposed ℝ P {v} → v ∈ F.val → l v = 1 := by
  have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices d P hP
  constructor
  · intro hsub v _ hvF
    exact hsub hvF
  · intro hv
    rw [hHull.2 F]
    refine convexHull_min ?_ (convex_hyperplane l.toLinearMap.isLinear 1)
    rintro v ⟨hvF, hvExp⟩
    exact hv v hvExp hvF

/-- Cost bound for a single facet-discovery phase with `k` already discovered facets. -/
def facetPhaseCost (d m k : ℕ) : ℕ :=
  1 + (d - 1) * (2 * (m - k) + 3)

/-- Potential function for a phased vertex-certification and facet-discovery execution. -/
def phasePotential (d m V_card : ℕ) (S : Finset (Fin m)) (C_card q : ℕ) : ℕ :=
  q + (V_card - C_card) + ∑ k ∈ Finset.Ico S.card m, facetPhaseCost d m k

lemma phasePotential_certify_step {d m : ℕ} {V : Finset (Fin d → ℝ)}
    (S : Finset (Fin m)) {C : Finset (Fin d → ℝ)} (hCV : C ⊆ V)
    {v : Fin d → ℝ} (hvV : v ∈ V) (hvC : v ∉ C)
    {q q' : ℕ} (hq' : q' ≤ q + 1) :
    insert v C ⊆ V ∧
    phasePotential d m V.card S (insert v C).card q' ≤
      phasePotential d m V.card S C.card q := by
  have hins : insert v C ⊆ V := Finset.insert_subset_iff.2 ⟨hvV, hCV⟩
  have hcard_ins : (insert v C).card = C.card + 1 := Finset.card_insert_of_notMem hvC
  have hcard_le : C.card + 1 ≤ V.card := by
    rw [← hcard_ins]
    exact Finset.card_le_card hins
  refine ⟨hins, ?_⟩
  unfold phasePotential
  rw [hcard_ins]
  omega

lemma phasePotential_discover_step {d m : ℕ} (V_card : ℕ)
    (S : Finset (Fin m)) {i_new : Fin m} (hi : i_new ∉ S)
    (C_card : ℕ) {q q' : ℕ} (hq' : q' ≤ q + facetPhaseCost d m S.card) :
    phasePotential d m V_card (insert i_new S) C_card q' ≤
      phasePotential d m V_card S C_card q := by
  have hcard_ins : (insert i_new S).card = S.card + 1 := Finset.card_insert_of_notMem hi
  have hcard_lt : S.card < m := by
    have hle : (insert i_new S).card ≤ (Finset.univ : Finset (Fin m)).card :=
      Finset.card_le_univ (insert i_new S)
    rw [Finset.card_fin, hcard_ins] at hle
    omega
  have hsum_split : ∑ k ∈ Finset.Ico S.card m, facetPhaseCost d m k =
      facetPhaseCost d m S.card +
        ∑ k ∈ Finset.Ico (S.card + 1) m, facetPhaseCost d m k := by
    rw [← Finset.sum_Ico_consecutive _ (Nat.le_succ S.card) hcard_lt, Nat.Ico_succ_singleton,
      Finset.sum_singleton]
  unfold phasePotential
  rw [hcard_ins, hsum_split]
  omega

lemma phasePotential_init_bound (d m V_card : ℕ) (S₀ : Finset (Fin m)) (C₀_card q₀ : ℕ)
    (hq₀ : q₀ ≤ d + 1) :
    phasePotential d m V_card S₀ C₀_card q₀ ≤
      V_card + (d + 1) + ∑ k ∈ Finset.range m, facetPhaseCost d m k := by
  have hsub : Finset.Ico S₀.card m ⊆ Finset.range m := by
    intro k hk
    exact Finset.mem_range.2 (Finset.mem_Ico.1 hk).2
  have hsum_le : ∑ k ∈ Finset.Ico S₀.card m, facetPhaseCost d m k ≤
      ∑ k ∈ Finset.range m, facetPhaseCost d m k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  unfold phasePotential
  omega

/-- Inductive query bound for any sequence of `N` phases, each either certifying a fresh
exposed vertex of `P` at query cost `≤ 1` or discovering a fresh facet of `P` at query cost
`≤ 1 + (d - 1) * (2 * (m - S_t.card) + 3)`. -/
lemma phased_trace_query_bound {d m : ℕ} (V : Finset (Fin d → ℝ))
    (N : ℕ)
    (S_seq : ℕ → Finset (Fin m))
    (C_seq : ℕ → Finset (Fin d → ℝ))
    (q_seq : ℕ → ℕ)
    (hC₀ : C_seq 0 ⊆ V)
    (hq₀ : q_seq 0 ≤ d + 1)
    (hStep : ∀ t < N,
      (S_seq (t + 1) = S_seq t ∧
        ∃ v ∈ V, v ∉ C_seq t ∧ C_seq (t + 1) = insert v (C_seq t) ∧
          q_seq (t + 1) ≤ q_seq t + 1) ∨
      (C_seq (t + 1) = C_seq t ∧
        ∃ i_new : Fin m, i_new ∉ S_seq t ∧ S_seq (t + 1) = insert i_new (S_seq t) ∧
          q_seq (t + 1) ≤ q_seq t + facetPhaseCost d m (S_seq t).card)) :
    C_seq N ⊆ V ∧
    q_seq N ≤ V.card + (d + 1) + ∑ k ∈ Finset.range m, facetPhaseCost d m k := by
  have h_inv : ∀ t ≤ N,
      C_seq t ⊆ V ∧
      phasePotential d m V.card (S_seq t) (C_seq t).card (q_seq t) ≤
        phasePotential d m V.card (S_seq 0) (C_seq 0).card (q_seq 0) := by
    intro t ht
    induction t with
    | zero => exact ⟨hC₀, le_rfl⟩
    | succ t ih =>
      obtain ⟨hCt, hPot_t⟩ := ih (Nat.le_of_succ_le ht)
      rcases hStep t (Nat.lt_of_succ_le ht) with
        ⟨hS_eq, v, hvV, hvC, hC_eq, hq_le⟩ | ⟨hC_eq, i_new, hi, hS_eq, hq_le⟩
      · obtain ⟨hC_next, hPot_step⟩ :=
          phasePotential_certify_step (S_seq t) hCt hvV hvC hq_le
        have hPot_step' :
            phasePotential d m V.card (S_seq (t + 1)) (C_seq (t + 1)).card (q_seq (t + 1)) ≤
              phasePotential d m V.card (S_seq t) (C_seq t).card (q_seq t) := by
          rw [hS_eq, hC_eq]
          exact hPot_step
        exact ⟨hC_eq ▸ hC_next, hPot_step'.trans hPot_t⟩
      · have hPot_step :=
          phasePotential_discover_step V.card (S_seq t) hi (C_seq t).card hq_le
        have hPot_step' :
            phasePotential d m V.card (S_seq (t + 1)) (C_seq (t + 1)).card (q_seq (t + 1)) ≤
              phasePotential d m V.card (S_seq t) (C_seq t).card (q_seq t) := by
          rw [hS_eq, hC_eq]
          exact hPot_step
        exact ⟨hC_eq ▸ hCt, hPot_step'.trans hPot_t⟩
  obtain ⟨hCN, hPotN⟩ := h_inv N le_rfl
  have hInit := phasePotential_init_bound d m V.card (S_seq 0) (C_seq 0).card (q_seq 0) hq₀
  have hq_le_pot : q_seq N ≤ phasePotential d m V.card (S_seq N) (C_seq N).card (q_seq N) := by
    unfold phasePotential
    omega
  exact ⟨hCN, (hq_le_pot.trans hPotN).trans hInit⟩

lemma isDPolytope_convex_and_isClosed {d : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    {m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (hP_L : P = {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1}) :
    Convex ℝ P ∧ IsClosed P := by
  rcases hP.1 with ⟨V, _, _, rfl⟩
  refine ⟨convex_convexHull ℝ V, ?_⟩
  rw [hP_L]
  have h_eq : {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1} =
      ⋂ i : Fin m, {x : Fin d → ℝ | L i x ≤ 1} := by
    ext x; simp
  rw [h_eq]
  exact isClosed_iInter (fun i => isClosed_le (L i).continuous continuous_const)

end Grunbaum2003

open Grunbaum2003

theorem solution (d : ℕ) (hd : 2 ≤ d) :
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)}, IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ),
        P = {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1} →
        ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
          (P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} ∧
            faceCount P 0 = (P.extremePoints ℝ).ncard) ∧
          (∀ (F : PolytopeFace P) (i : Fin m),
            F.val ⊆ {x : Fin d → ℝ | L i x = 1} ↔
              ∀ v : Fin d → ℝ, IsExposed ℝ P {v} → v ∈ F.val → L i v = 1) ∧
          (∀ S : Finset (Fin m),
            P ⊆ {x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1} ∧
            P ∩ ({x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ ⊆ P.extremePoints ℝ ∧
            ∀ {v : Fin d → ℝ},
              v ∈ ({x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ →
              oracle v ≠ v →
              ∀ {i_new : Fin m}, L i_new (oracle v) = 1 →
                i_new ∉ S ∧ (insert i_new S).card = S.card + 1) ∧
          (∀ (S : Finset (Fin m)) (V_Q C : Set (Fin d → ℝ)),
            {x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1} = convexHull ℝ V_Q →
            V_Q ⊆ C → C ⊆ P.extremePoints ℝ →
            ({x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ ⊆ C →
            {x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1} = P ∧ C = P.extremePoints ℝ)) ∧
    (∀ (program : List RayInstruction) (P : Set (Fin d → ℝ)),
      IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ (oracle : (Fin d → ℝ) → (Fin d → ℝ)), IsPolytopeRayOracle P oracle →
        ∀ (L : Fin (faceCount P (d - 1)) → (Fin d → ℝ) →L[ℝ] ℝ),
          P = {x | ∀ i, L i x ≤ 1} →
          ∀ (t : ℕ) (c : RayConfiguration) (n : ℕ) (e : Fin n ≃ PolytopeFace P)
            (N : ℕ)
            (S_seq : ℕ → Finset (Fin (faceCount P (d - 1))))
            (C_seq : ℕ → Finset (Fin d → ℝ))
            (q_seq : ℕ → ℕ),
            rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c →
            program[c.pc]? = some .halt →
            C_seq 0 = ∅ →
            q_seq 0 ≤ d + 1 →
            (∀ s < N,
              (S_seq (s + 1) = S_seq s ∧
                ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                  v ∈ P ∧ v ∉ C_seq s ∧ C_seq (s + 1) = insert v (C_seq s) ∧
                  q_seq (s + 1) ≤ q_seq s + 1) ∨
              (C_seq (s + 1) = C_seq s ∧
                ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                  oracle v ≠ v ∧
                  ∃ i_new : Fin (faceCount P (d - 1)),
                    L i_new (oracle v) = 1 ∧
                    S_seq (s + 1) = insert i_new (S_seq s) ∧
                    q_seq (s + 1) ≤ q_seq s +
                      (1 + (d - 1) * (2 * (faceCount P (d - 1) - (S_seq s).card) + 3)))) →
            c.queries ≤ q_seq N →
            (∀ i : Fin n, c.tape (c.head + (i.val : ℤ)) = 1) →
            c.tape (c.head + (n : ℤ)) = 0 →
            (∀ i j : Fin n,
              c.tape (c.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
                if (∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val)
                then 1 else 0) →
            rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
            program[c.pc]? = some .halt ∧
            c.queries ≤ faceCount P 0 + (d + 1) +
              ∑ k ∈ Finset.range (faceCount P (d - 1)),
                (1 + (d - 1) * (2 * (faceCount P (d - 1) - k) + 3)) ∧
            (∀ i : Fin n, c.tape (c.head + (i.val : ℤ)) = 1) ∧
            c.tape (c.head + (n : ℤ)) = 0 ∧
            ∀ i j : Fin n,
              c.tape (c.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
                if (∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val)
                then 1 else 0) := by
  have hd_pos : 0 < d := by omega
  refine ⟨?_, ?_⟩
  · intro m P hP h0 L hP_L oracle hOracle
    obtain ⟨hConv, hClosed⟩ := isDPolytope_convex_and_isClosed hP L hP_L
    refine ⟨extremePoints_eq_exposed_singletons_of_isDPolytope hP,
      fun F i => face_subset_hyperplane_iff_exposed_vertices_eq_one hP F (L i),
      fun S => ?_, fun S V_Q C hQ hVQ_C hC_ext hExt_C => ?_⟩
    · have hPQ := subset_outerHalfspacePolytope L hP_L S
      have hPersist := (certified_extremePoints_persist hPQ (Set.Subset.refl _)).2
      refine ⟨hPQ, hPersist, fun hv hne _ hi_new => ?_⟩
      exact fresh_facet_of_failed_extreme_verification hd_pos hConv hClosed h0 L hP_L
        hOracle S hv hne hi_new
    · exact outer_polytope_and_certified_vertices_eq_of_all_verified
        hConv (subset_outerHalfspacePolytope L hP_L S) hQ hVQ_C hC_ext hExt_C
  · intro program P hP h0 oracle hOracle L hP_L t c n e N S_seq C_seq q_seq
      hRun hHalt hC₀ hq₀ hStep hqN hHead1 hHead0 hTable
    obtain ⟨hConv, hClosed⟩ := isDPolytope_convex_and_isClosed hP L hP_L
    have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices d P hP
    have hVBound := Grunbaum2003.polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound d P
    have hExtEq := (extremePoints_eq_exposed_singletons_of_isDPolytope hP).1
    let V_set : Set (Fin d → ℝ) := {x : Fin d → ℝ | IsExposed ℝ P {x}}
    have hV_fin : V_set.Finite := hHull.1
    let V : Finset (Fin d → ℝ) := hV_fin.toFinset
    have hCardV : faceCount P 0 = V.card := by
      rw [hVBound.1, Set.ncard_eq_toFinset_card V_set hV_fin]
    have hC₀_sub : C_seq 0 ⊆ V := by
      rw [hC₀]; exact Finset.empty_subset V
    have hStep' : ∀ s < N,
        (S_seq (s + 1) = S_seq s ∧
          ∃ v ∈ V, v ∉ C_seq s ∧ C_seq (s + 1) = insert v (C_seq s) ∧
            q_seq (s + 1) ≤ q_seq s + 1) ∨
        (C_seq (s + 1) = C_seq s ∧
          ∃ i_new : Fin (faceCount P (d - 1)),
            i_new ∉ S_seq s ∧ S_seq (s + 1) = insert i_new (S_seq s) ∧
            q_seq (s + 1) ≤ q_seq s +
              facetPhaseCost d (faceCount P (d - 1)) (S_seq s).card) := by
      intro s hs
      rcases hStep s hs with
        ⟨hS_eq, v, hv_extQ, hvP, hvC, hC_eq, hq_le⟩ |
        ⟨hC_eq, v, hv_extQ, hne, i_new, hi_new, hS_eq, hq_le⟩
      · left
        have hPQ := subset_outerHalfspacePolytope L hP_L (S_seq s)
        have hv_extP : v ∈ P.extremePoints ℝ :=
          (certified_extremePoints_persist hPQ (Set.Subset.refl _)).2 ⟨hvP, hv_extQ⟩
        rw [hExtEq] at hv_extP
        have hvV : v ∈ V := hV_fin.mem_toFinset.2 hv_extP
        exact ⟨hS_eq, v, hvV, hvC, hC_eq, hq_le⟩
      · right
        have hFresh := fresh_facet_of_failed_extreme_verification hd_pos hConv hClosed h0
          L hP_L hOracle (S_seq s) hv_extQ hne hi_new
        exact ⟨hC_eq, i_new, hFresh.1, hS_eq, hq_le⟩
    have hBound := (phased_trace_query_bound V N S_seq C_seq q_seq hC₀_sub hq₀ hStep').2
    rw [← hCardV] at hBound
    exact ⟨hRun, hHalt, hqN.trans hBound, hHead1, hHead0, hTable⟩
