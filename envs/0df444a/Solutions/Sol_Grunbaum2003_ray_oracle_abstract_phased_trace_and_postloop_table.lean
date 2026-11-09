-- Prove2me | solution 1 for Grunbaum2003.ray_oracle_abstract_phased_trace_and_postloop_table
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T01:28:58.771327+00:00
-- url     : https://prove2.me/submissions/cb13276f-cac8-4f3c-b519-427cd14ae3f3

import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Theorems.Thm_Grunbaum2003_rayOracle_local_sector_and_known_facet_exclusion
import Theorems.Thm_Grunbaum2003_rayFrame_boundary_extension_axes_and_cramer_normal
import Theorems.Thm_Grunbaum2003_ray_oracle_outer_polytope_invariants_and_phased_trace_bound
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Theorems.Thm_Grunbaum2003_polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Data.Finset.Card
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators Matrix
open Classical

namespace Grunbaum2003

/-- Outer halfspace approximation defined by a subset `S` of facet indices. -/
def outerHalfspace {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (S : Finset (Fin m)) : Set (Fin d → ℝ) :=
  {x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}

lemma outerHalfspace_convex_and_closed {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (S : Finset (Fin m)) :
    Convex ℝ (outerHalfspace L S) ∧ IsClosed (outerHalfspace L S) := by
  have h_eq : outerHalfspace L S = ⋂ i ∈ S, {x : Fin d → ℝ | L i x ≤ 1} := by
    ext x; simp [outerHalfspace]
  rw [h_eq]
  refine ⟨convex_iInter (fun i => convex_iInter (fun _ => convex_halfSpace_le (L i).toLinearMap.isLinear 1)),
    isClosed_biInter (fun i _ => isClosed_le (L i).continuous continuous_const)⟩

lemma outerHalfspace_antitone' {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {S₁ S₂ : Finset (Fin m)} (h : S₁ ⊆ S₂) :
    outerHalfspace L S₂ ⊆ outerHalfspace L S₁ := by
  intro x hx i hi
  exact hx i (h hi)

lemma exists_active_facet_of_mem_frontier {d m : ℕ}
    {P : Set (Fin d → ℝ)} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (hP : P = {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1})
    {y : Fin d → ℝ} (hy : y ∈ frontier P) :
    ∃ i : Fin m, L i y = 1 := by
  have hyP : y ∈ P := by
    have hClosed : IsClosed P := by
      rw [hP]
      have h_eq : {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1} =
          ⋂ i : Fin m, {x : Fin d → ℝ | L i x ≤ 1} := by ext x; simp
      rw [h_eq]
      exact isClosed_iInter (fun i => isClosed_le (L i).continuous continuous_const)
    rw [hClosed.frontier_eq] at hy
    exact hy.1
  have hy_not_int : y ∉ interior P := hy.2
  by_contra h_none
  have hy_lt : ∀ i : Fin m, L i y < 1 := by
    intro i
    have hle : L i y ≤ 1 := by rw [hP] at hyP; exact hyP i
    exact lt_of_le_of_ne hle (fun heq => h_none ⟨i, heq⟩)
  let U : Set (Fin d → ℝ) := ⋂ i : Fin m, {x : Fin d → ℝ | L i x < 1}
  have hU_open : IsOpen U :=
    isOpen_iInter_of_finite (fun i => isOpen_lt (L i).continuous continuous_const)
  have hU_sub : U ⊆ P := by
    intro x hx
    rw [hP]
    intro i
    exact le_of_lt (Set.mem_iInter.1 hx i)
  have hyU : y ∈ U := Set.mem_iInter.2 hy_lt
  exact hy_not_int (mem_interior.2 ⟨U, hU_sub, hU_open, hyU⟩)

lemma compact_outerHalfspace_eq_of_extremePoints_subset {d m : ℕ}
    {P : Set (Fin d → ℝ)} (hP_conv : Convex ℝ P) (hP_closed : IsClosed P)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (hP : P = {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1})
    (S : Finset (Fin m)) (hComp : IsCompact (outerHalfspace L S))
    {C : Set (Fin d → ℝ)} (hC_extP : C ⊆ P.extremePoints ℝ)
    (hExtQ_C : (outerHalfspace L S).extremePoints ℝ ⊆ C) :
    outerHalfspace L S = P ∧ C = P.extremePoints ℝ := by
  obtain ⟨hQ_conv, _⟩ := outerHalfspace_convex_and_closed L S
  have hPQ : P ⊆ outerHalfspace L S := by
    intro x hx i hi; rw [hP] at hx; exact hx i
  have hC_P : C ⊆ P := fun x hx => (hC_extP hx).1
  have hKM : closure (convexHull ℝ ((outerHalfspace L S).extremePoints ℝ)) = outerHalfspace L S :=
    closure_convexHull_extremePoints hComp hQ_conv
  have hHull_sub : convexHull ℝ ((outerHalfspace L S).extremePoints ℝ) ⊆ P :=
    convexHull_min (hExtQ_C.trans hC_P) hP_conv
  have hQP : outerHalfspace L S ⊆ P := by
    rw [← hKM]
    exact hP_closed.closure_subset_iff.2 hHull_sub
  have hQP_eq : outerHalfspace L S = P := Set.Subset.antisymm hQP hPQ
  refine ⟨hQP_eq, Set.Subset.antisymm hC_extP ?_⟩
  rw [← hQP_eq]
  exact hExtQ_C

lemma exists_phased_outer_polytope_trace_from {d m : ℕ} (hd : 2 ≤ d)
    {P : Set (Fin d → ℝ)} (hP : IsDPolytope P) (h0 : (0 : Fin d → ℝ) ∈ interior P)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (hP_L : P = {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)} (hOracle : IsPolytopeRayOracle P oracle)
    (V : Finset (Fin d → ℝ)) (hV : (V : Set (Fin d → ℝ)) = P.extremePoints ℝ) :
    ∀ (K : ℕ) (S : Finset (Fin m)) (C : Finset (Fin d → ℝ)) (q : ℕ),
      outerHalfspace L S = P →
      C ⊆ V →
      (m - S.card) + (V.card - C.card) ≤ K →
      ∃ (N : ℕ)
        (S_seq : ℕ → Finset (Fin m))
        (C_seq : ℕ → Finset (Fin d → ℝ))
        (q_seq : ℕ → ℕ),
        S_seq 0 = S ∧
        C_seq 0 = C ∧
        q_seq 0 = q ∧
        (∀ s < N,
          (S_seq (s + 1) = S_seq s ∧
            ∃ v ∈ (outerHalfspace L (S_seq s)).extremePoints ℝ,
              v ∈ P ∧ v ∉ C_seq s ∧ C_seq (s + 1) = insert v (C_seq s) ∧
              q_seq (s + 1) ≤ q_seq s + 1) ∨
          (C_seq (s + 1) = C_seq s ∧
            ∃ v ∈ (outerHalfspace L (S_seq s)).extremePoints ℝ,
              oracle v ≠ v ∧
              ∃ i_new : Fin m,
                L i_new (oracle v) = 1 ∧
                S_seq (s + 1) = insert i_new (S_seq s) ∧
                q_seq (s + 1) ≤ q_seq s +
                  (1 + (d - 1) * (2 * (m - (S_seq s).card) + 3)))) ∧
        outerHalfspace L (S_seq N) = P ∧
        C_seq N = V := by
  have hd_pos : 0 < d := by omega
  have hInv := (Grunbaum2003.ray_oracle_outer_polytope_invariants_and_phased_trace_bound d hd).1
    hP h0 L hP_L hOracle
  have hP_conv : Convex ℝ P := by
    rcases hP.1 with ⟨W, _, _, rfl⟩
    exact convex_convexHull ℝ W
  have hP_closed : IsClosed P := by
    rw [hP_L]
    have h_eq : {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1} =
        ⋂ i : Fin m, {x : Fin d → ℝ | L i x ≤ 1} := by ext x; simp
    rw [h_eq]
    exact isClosed_iInter (fun i => isClosed_le (L i).continuous continuous_const)
  intro K
  induction K with
  | zero =>
    intro S C q hQP hCV hK
    have hExt_sub : (outerHalfspace L S).extremePoints ℝ ⊆ (C : Set (Fin d → ℝ)) := by
      intro v hv
      by_contra hvC
      have hvC' : v ∉ C := hvC
      have hvP : v ∈ P := by rw [← hQP]; exact hv.1
      have hPersist := hInv.2.2.1 S
      have hv_extP : v ∈ P.extremePoints ℝ := hPersist.2.1 ⟨hvP, hv⟩
      rw [← hV] at hv_extP
      have hvV : v ∈ V := hv_extP
      have hlt : C.card < V.card := Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.2 ⟨hCV, fun h_eq => hvC' (h_eq ▸ hvV)⟩)
      omega
    have hVC : V ⊆ C := by
      rw [← Finset.coe_subset, hV, ← hQP]
      exact hExt_sub
    have hCV_eq : C = V := Finset.Subset.antisymm hCV hVC
    refine ⟨0, fun _ => S, fun _ => C, fun _ => q, rfl, rfl, rfl, ?_, hQP, hCV_eq⟩
    intro s hs; omega
  | succ K ih =>
    intro S C q hQP hCV hK
    by_cases hAll : (outerHalfspace L S).extremePoints ℝ ⊆ (C : Set (Fin d → ℝ))
    · have hVC : V ⊆ C := by
        rw [← Finset.coe_subset, hV, ← hQP]
        exact hAll
      have hCV_eq : C = V := Finset.Subset.antisymm hCV hVC
      refine ⟨0, fun _ => S, fun _ => C, fun _ => q, rfl, rfl, rfl, ?_, hQP, hCV_eq⟩
      intro s hs; omega
    · obtain ⟨v, hv, hvC⟩ := Set.not_subset.1 hAll
      have hvC' : v ∉ C := hvC
      have hvP : v ∈ P := by rw [← hQP]; exact hv.1
      have hPersist := hInv.2.2.1 S
      have hv_extP : v ∈ P.extremePoints ℝ := hPersist.2.1 ⟨hvP, hv⟩
      rw [← hV] at hv_extP
      have hvV : v ∈ V := hv_extP
      have hins_sub : insert v C ⊆ V := Finset.insert_subset_iff.2 ⟨hvV, hCV⟩
      have hcard_ins : (insert v C).card = C.card + 1 := Finset.card_insert_of_notMem hvC'
      have hcard_le : C.card + 1 ≤ V.card := by
        rw [← hcard_ins]
        exact Finset.card_le_card hins_sub
      have hK' : (m - S.card) + (V.card - (insert v C).card) ≤ K := by omega
      obtain ⟨N, S_seq, C_seq, q_seq, hS₀, hC₀, hq₀, hStep, hQN, hCN⟩ :=
        ih S (insert v C) (q + 1) hQP hins_sub hK'
      refine ⟨N + 1,
        fun s => Nat.casesOn s S S_seq,
        fun s => Nat.casesOn s C C_seq,
        fun s => Nat.casesOn s q q_seq,
        rfl, rfl, rfl, ?_, hQN, hCN⟩
      intro s hs
      cases s with
      | zero =>
        left
        change S_seq 0 = S ∧ ∃ v' ∈ (outerHalfspace L S).extremePoints ℝ,
          v' ∈ P ∧ v' ∉ C ∧ C_seq 0 = insert v' C ∧ q_seq 0 ≤ q + 1
        exact ⟨hS₀, v, hv, hvP, hvC', hC₀, by omega⟩
      | succ s =>
        exact hStep s (Nat.lt_of_succ_lt_succ hs)

lemma exists_phased_outer_polytope_trace {d m : ℕ} (hd : 2 ≤ d)
    {P : Set (Fin d → ℝ)} (hP : IsDPolytope P) (h0 : (0 : Fin d → ℝ) ∈ interior P)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (hP_L : P = {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)} (hOracle : IsPolytopeRayOracle P oracle)
    (q₀ : ℕ) (hq₀ : q₀ ≤ d + 1) :
    ∃ (V : Finset (Fin d → ℝ))
      (N : ℕ)
      (S_seq : ℕ → Finset (Fin m))
      (C_seq : ℕ → Finset (Fin d → ℝ))
      (q_seq : ℕ → ℕ),
      (V : Set (Fin d → ℝ)) = P.extremePoints ℝ ∧
      (V : Set (Fin d → ℝ)) = {x : Fin d → ℝ | IsExposed ℝ P {x}} ∧
      V.card = faceCount P 0 ∧
      C_seq 0 = ∅ ∧
      q_seq 0 ≤ d + 1 ∧
      (∀ s < N,
        (S_seq (s + 1) = S_seq s ∧
          ∃ v ∈ (outerHalfspace L (S_seq s)).extremePoints ℝ,
            v ∈ P ∧ v ∉ C_seq s ∧ C_seq (s + 1) = insert v (C_seq s) ∧
            q_seq (s + 1) ≤ q_seq s + 1) ∨
        (C_seq (s + 1) = C_seq s ∧
          ∃ v ∈ (outerHalfspace L (S_seq s)).extremePoints ℝ,
            oracle v ≠ v ∧
            ∃ i_new : Fin m,
              L i_new (oracle v) = 1 ∧
              S_seq (s + 1) = insert i_new (S_seq s) ∧
              q_seq (s + 1) ≤ q_seq s +
                (1 + (d - 1) * (2 * (m - (S_seq s).card) + 3)))) ∧
      outerHalfspace L (S_seq N) = P ∧
      C_seq N = V := by
  have hInv := (Grunbaum2003.ray_oracle_outer_polytope_invariants_and_phased_trace_bound d hd).1
    hP h0 L hP_L hOracle
  have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices d P hP
  have hVBound := Grunbaum2003.polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound d P
  let V_set : Set (Fin d → ℝ) := {x : Fin d → ℝ | IsExposed ℝ P {x}}
  have hV_fin : V_set.Finite := hHull.1
  let V : Finset (Fin d → ℝ) := hV_fin.toFinset
  have hV_coe : (V : Set (Fin d → ℝ)) = V_set := hV_fin.coe_toFinset
  have hV_ext : (V : Set (Fin d → ℝ)) = P.extremePoints ℝ := by
    rw [hV_coe, hInv.1.1]
  have hV_card : V.card = faceCount P 0 := by
    rw [hVBound.1, Set.ncard_eq_toFinset_card V_set hV_fin]
  have hQP₀ : outerHalfspace L (Finset.univ : Finset (Fin m)) = P := by
    rw [hP_L]; ext x; simp [outerHalfspace]
  obtain ⟨N, S_seq, C_seq, q_seq, _, hC₀, hq₀_eq, hStep, hQN, hCN⟩ :=
    exists_phased_outer_polytope_trace_from hd hP h0 L hP_L hOracle V hV_ext
      ((m - (Finset.univ : Finset (Fin m)).card) + V.card) Finset.univ ∅ q₀ hQP₀
      (Finset.empty_subset V) (by simp)
  exact ⟨V, N, S_seq, C_seq, q_seq, hV_ext, hV_coe, hV_card, hC₀, hq₀_eq ▸ hq₀,
    hStep, hQN, hCN⟩

lemma face_exposed_vertex_inclusion_iff_fin {d n V : ℕ} {P : Set (Fin d → ℝ)}
    (vEnum : Fin V ≃ {x : Fin d → ℝ | IsExposed ℝ P {x}})
    (e : Fin n ≃ PolytopeFace P) (i j : Fin n) :
    (∀ k : Fin V, (vEnum k).val ∈ (e i).val → (vEnum k).val ∈ (e j).val) ↔
      (∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val) := by
  constructor
  · intro hall x hx hxi
    simpa using hall (vEnum.symm ⟨x, hx⟩) (by simpa using hxi)
  · intro hall k hki
    exact hall (vEnum k).val (vEnum k).property hki

lemma rayMachine_postloop_incidence_and_table_composition {d : ℕ}
    (run_add : ∀ (program : List RayInstruction)
      (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
      rayMachineRun program oracle (a + b) c =
        (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
    (relocateInst : ℕ → RayInstruction → RayInstruction)
    (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
    (hRelocate : ∀ (pre program : List RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
      (relocateCfg pre.length c).pc = pre.length + c.pc ∧
      (relocateCfg pre.length c).head = c.head ∧
      (relocateCfg pre.length c).tape = c.tape ∧
      (relocateCfg pre.length c).queries = c.queries ∧
      rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
          (relocateCfg pre.length c) =
        (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
      (program[c.pc]? = some .halt →
        (pre ++ program.map (relocateInst pre.length))[
          (relocateCfg pre.length c).pc]? = some .halt))
    (headerAndInclusionTableProgram : ℕ → ℕ → ℤ → ℤ → List RayInstruction)
    (headerAndInclusionTableDest : ℕ → ℕ → ℤ → ℤ → ℤ)
    (headerAndInclusionTableSteps : ℕ → ℕ → ℤ → ℕ)
    (hTableProg : ∀ {n V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (fvBase minBase : ℤ) (q : ℕ) (inc : Fin n → Fin V → Prop),
      (∀ (a : Fin n) (k : Fin V),
        source (fvBase + (a.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
          if inc a k then (1 : ℝ) else 0) →
      let prog := headerAndInclusionTableProgram n V fvBase minBase
      let outBase := headerAndInclusionTableDest n V fvBase minBase
      let steps := headerAndInclusionTableSteps n V fvBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = outBase ∧ c'.queries = q ∧
        (∀ i : Fin n, c'.tape (c'.head + (i.val : ℤ)) = 1) ∧
        c'.tape (c'.head + (n : ℤ)) = 0 ∧
        (∀ i j : Fin n,
          c'.tape (c'.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
            if (∀ k : Fin V, inc i k → inc j k) then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < c'.head → c'.tape z = source z))
    {P : Set (Fin d → ℝ)} {n V : ℕ}
    (vEnum : Fin V ≃ {x : Fin d → ℝ | IsExposed ℝ P {x}})
    (e : Fin n ≃ PolytopeFace P)
    (pre : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (t_pre : ℕ) (c_pre : RayConfiguration) (fvBase minBase : ℤ)
    (hRun_pre : rayMachineRun (pre ++
        (headerAndInclusionTableProgram n V fvBase minBase).map (relocateInst pre.length))
      oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
        some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩))
    (hInc_pre : ∀ (a : Fin n) (k : Fin V),
      c_pre.tape (fvBase + (a.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
        if (vEnum k).val ∈ (e a).val then (1 : ℝ) else 0) :
    let prog := pre ++
      (headerAndInclusionTableProgram n V fvBase minBase).map (relocateInst pre.length)
    ∃ (t : ℕ) (c : RayConfiguration),
      rayMachineRun prog oracle t
        { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
      prog[c.pc]? = some .halt ∧
      c.queries = c_pre.queries ∧
      (∀ i : Fin n, c.tape (c.head + (i.val : ℤ)) = 1) ∧
      c.tape (c.head + (n : ℤ)) = 0 ∧
      ∀ i j : Fin n,
        c.tape (c.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
          if (∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val)
          then 1 else 0 := by
  intro prog
  let inc : Fin n → Fin V → Prop := fun a k => (vEnum k).val ∈ (e a).val
  let t_tab := headerAndInclusionTableSteps n V fvBase
  obtain ⟨_, c_tab, hRun_tab, _, hHalt_tab, hHead_tab, hQ_tab, h1_tab, h0_tab, hMat_tab, _⟩ :=
    hTableProg oracle c_pre.tape fvBase minBase c_pre.queries inc hInc_pre
  have hRel := hRelocate pre (headerAndInclusionTableProgram n V fvBase minBase) oracle t_tab
    ⟨0, 0, c_pre.tape, c_pre.queries⟩
  have hRel_tab := hRelocate pre (headerAndInclusionTableProgram n V fvBase minBase) oracle 0 c_tab
  refine ⟨t_pre + t_tab, relocateCfg pre.length c_tab, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_add, hRun_pre, Option.bind_some, hRel.2.2.2.2.1, hRun_tab, Option.map_some]
  · exact hRel_tab.2.2.2.2.2 hHalt_tab
  · rw [hRel_tab.2.2.2.1, hQ_tab]
  · intro i
    rw [hRel_tab.2.1, hRel_tab.2.2.1]
    exact h1_tab i
  · rw [hRel_tab.2.1, hRel_tab.2.2.1]
    exact h0_tab
  · intro i j
    rw [hRel_tab.2.1, hRel_tab.2.2.1, hMat_tab i j]
    congr 1
    exact propext (face_exposed_vertex_inclusion_iff_fin vEnum e i j)

end Grunbaum2003

open Grunbaum2003

theorem solution (d : ℕ) (hd : 2 ≤ d) :
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)}, IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ),
        P = {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1} →
        ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
          ∃ (V : Finset (Fin d → ℝ))
            (N : ℕ)
            (S_seq : ℕ → Finset (Fin m))
            (C_seq : ℕ → Finset (Fin d → ℝ))
            (q_seq : ℕ → ℕ),
            (V : Set (Fin d → ℝ)) = P.extremePoints ℝ ∧
            (V : Set (Fin d → ℝ)) = {x : Fin d → ℝ | IsExposed ℝ P {x}} ∧
            V.card = faceCount P 0 ∧
            C_seq 0 = ∅ ∧
            q_seq 0 ≤ d + 1 ∧
            (∀ s < N,
              (S_seq (s + 1) = S_seq s ∧
                ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                  v ∈ P ∧ v ∉ C_seq s ∧ C_seq (s + 1) = insert v (C_seq s) ∧
                  q_seq (s + 1) ≤ q_seq s + 1) ∨
              (C_seq (s + 1) = C_seq s ∧
                ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                  oracle v ≠ v ∧
                  ∃ i_new : Fin m,
                    L i_new (oracle v) = 1 ∧
                    S_seq (s + 1) = insert i_new (S_seq s) ∧
                    q_seq (s + 1) ≤ q_seq s +
                      (1 + (d - 1) * (2 * (m - (S_seq s).card) + 3)))) ∧
            {x : Fin d → ℝ | ∀ i ∈ S_seq N, L i x ≤ 1} = P ∧
            C_seq N = V) ∧
    (∀ (run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration),
      (∀ (pre program : List RayInstruction)
        (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
        (relocateCfg pre.length c).pc = pre.length + c.pc ∧
        (relocateCfg pre.length c).head = c.head ∧
        (relocateCfg pre.length c).tape = c.tape ∧
        (relocateCfg pre.length c).queries = c.queries ∧
        rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
            (relocateCfg pre.length c) =
          (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
        (program[c.pc]? = some .halt →
          (pre ++ program.map (relocateInst pre.length))[
            (relocateCfg pre.length c).pc]? = some .halt)) →
      ∀ (headerAndInclusionTableProgram : ℕ → ℕ → ℤ → ℤ → List RayInstruction)
        (headerAndInclusionTableDest : ℕ → ℕ → ℤ → ℤ → ℤ)
        (headerAndInclusionTableSteps : ℕ → ℕ → ℤ → ℕ),
        (∀ {n V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (fvBase minBase : ℤ) (q : ℕ) (inc : Fin n → Fin V → Prop),
          (∀ (a : Fin n) (k : Fin V),
            source (fvBase + (a.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
              if inc a k then (1 : ℝ) else 0) →
          let prog := headerAndInclusionTableProgram n V fvBase minBase
          let outBase := headerAndInclusionTableDest n V fvBase minBase
          let steps := headerAndInclusionTableSteps n V fvBase
          minBase ≤ outBase ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
            c'.head = outBase ∧ c'.queries = q ∧
            (∀ i : Fin n, c'.tape (c'.head + (i.val : ℤ)) = 1) ∧
            c'.tape (c'.head + (n : ℤ)) = 0 ∧
            (∀ i j : Fin n,
              c'.tape (c'.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
                if (∀ k : Fin V, inc i k → inc j k) then (1 : ℝ) else 0) ∧
            (∀ z : ℤ, z < c'.head → c'.tape z = source z)) →
        ∀ {P : Set (Fin d → ℝ)} {n V : ℕ}
          (vEnum : Fin V ≃ {x : Fin d → ℝ | IsExposed ℝ P {x}})
          (e : Fin n ≃ PolytopeFace P)
          (pre : List RayInstruction)
          (oracle : (Fin d → ℝ) → (Fin d → ℝ))
          (t_pre : ℕ) (c_pre : RayConfiguration) (fvBase minBase : ℤ),
          rayMachineRun (pre ++
              (headerAndInclusionTableProgram n V fvBase minBase).map (relocateInst pre.length))
            oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
              some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
          (∀ (a : Fin n) (k : Fin V),
            c_pre.tape (fvBase + (a.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
              if (vEnum k).val ∈ (e a).val then (1 : ℝ) else 0) →
          let prog := pre ++
            (headerAndInclusionTableProgram n V fvBase minBase).map (relocateInst pre.length)
          ∃ (t : ℕ) (c : RayConfiguration),
            rayMachineRun prog oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
            prog[c.pc]? = some .halt ∧
            c.queries = c_pre.queries ∧
            (∀ i : Fin n, c.tape (c.head + (i.val : ℤ)) = 1) ∧
            c.tape (c.head + (n : ℤ)) = 0 ∧
            ∀ i j : Fin n,
              c.tape (c.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
                if (∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val)
                then 1 else 0) := by
  constructor
  · intro m P hP h0 L hP_L oracle hOracle
    exact exists_phased_outer_polytope_trace hd hP h0 L hP_L hOracle (d + 1) le_rfl
  · intro run_add relocateInst relocateCfg hRelocate
      headerAndInclusionTableProgram headerAndInclusionTableDest headerAndInclusionTableSteps
      hTableProg P n V vEnum e pre oracle t_pre c_pre fvBase minBase hRun_pre hInc_pre
    exact rayMachine_postloop_incidence_and_table_composition run_add relocateInst relocateCfg hRelocate
      headerAndInclusionTableProgram headerAndInclusionTableDest headerAndInclusionTableSteps
      hTableProg vEnum e pre oracle t_pre c_pre fvBase minBase hRun_pre hInc_pre
