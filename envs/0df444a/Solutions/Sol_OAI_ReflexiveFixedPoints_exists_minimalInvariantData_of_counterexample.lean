-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.exists_minimalInvariantData_of_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:01:17.198347+00:00
-- url     : https://prove2.me/submissions/9513ffde-b589-4171-aae6-3d7939ec922d

import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness

open OAI OAI.ReflexiveFixedPoints
open Set TopologicalSpace
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem rfp_chain
    {c : Set (Set X)} (hne : c.Nonempty) (hc : IsChain (· ⊆ ·) c)
    (hcompact : ∀ s ∈ c, WeaklyCompact s)
    (hclosed : ∀ s ∈ c, WeaklyClosed s)
    (hnonempty : ∀ s ∈ c, s.Nonempty) : (⋂₀ c).Nonempty := by
  haveI : Nonempty c := hne.to_subtype
  let e := toWeakSpace ℝ X
  let t : c → Set (WeakSpace ℝ X) := fun s => e '' (s : Set X)
  have htd : Directed (· ⊇ ·) t := by
    intro s1 s2
    rcases eq_or_ne (s1 : Set X) s2 with h | h
    · exact ⟨s1, le_rfl, by simp only [t, h]; exact le_rfl⟩
    · rcases hc s1.2 s2.2 h with h12 | h21
      · exact ⟨s1, le_rfl, Set.image_mono h12⟩
      · exact ⟨s2, Set.image_mono h21, le_rfl⟩
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd
    (fun s => (hnonempty s s.2).image _) (fun s => hcompact s s.2) (fun s => hclosed s s.2)
  refine ⟨e.symm y, ?_⟩
  rw [Set.mem_sInter]
  intro s hs
  have := Set.mem_iInter.mp hy ⟨s, hs⟩
  obtain ⟨x, hx, rfl⟩ := this
  simpa using hx

/-- One generation step: add images and rational convex combinations. -/
def rfpStep {C : Set X} (F : C → C) (Q : Set X) : Set X :=
  Q ∪ (fun x : C => (F x : X)) '' ((↑) ⁻¹' Q) ∪
    {z | ∃ r : ℚ, 0 < (r : ℝ) ∧ (r : ℝ) < 1 ∧ ∃ x ∈ Q, ∃ y ∈ Q, z = (r : ℝ) • x + (1 - (r : ℝ)) • y}

def rfpGen {C : Set X} (F : C → C) (x0 : X) : ℕ → Set X
  | 0 => {x0}
  | n + 1 => rfpStep F (rfpGen F x0 n)

theorem rfpGen_mono {C : Set X} (F : C → C) (x0 : X) : Monotone (rfpGen F x0) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  intro z hz
  show z ∈ rfpStep F (rfpGen F x0 n)
  exact Or.inl (Or.inl hz)

theorem rfpGen_countable {C : Set X} (F : C → C) (x0 : X) (n : ℕ) : (rfpGen F x0 n).Countable := by
  induction n with
  | zero => exact Set.countable_singleton _
  | succ n ih =>
    show (rfpStep F (rfpGen F x0 n)).Countable
    refine (ih.union ?_).union ?_
    · exact (ih.preimage Subtype.val_injective).image _
    · have : {z | ∃ r : ℚ, 0 < (r : ℝ) ∧ (r : ℝ) < 1 ∧ ∃ x ∈ rfpGen F x0 n, ∃ y ∈ rfpGen F x0 n,
          z = (r : ℝ) • x + (1 - (r : ℝ)) • y} ⊆
          (fun p : ℚ × X × X => (p.1 : ℝ) • p.2.1 + (1 - (p.1 : ℝ)) • p.2.2) ''
            ((Set.univ : Set ℚ) ×ˢ (rfpGen F x0 n ×ˢ rfpGen F x0 n)) := by
        rintro z ⟨r, -, -, x, hx, y, hy, rfl⟩
        exact ⟨(r, x, y), ⟨trivial, hx, hy⟩, rfl⟩
      exact ((Set.countable_univ.prod (ih.prod ih)).image _).mono this

theorem rfpGen_sub {C : Set X} (hconvex : Convex ℝ C) (F : C → C) (x0 : X) (hx0 : x0 ∈ C)
    (n : ℕ) : rfpGen F x0 n ⊆ C := by
  induction n with
  | zero => simpa [rfpGen] using hx0
  | succ n ih =>
    rintro z ((hz | ⟨x, -, rfl⟩) | ⟨r, hr0, hr1, x, hx, y, hy, rfl⟩)
    · exact ih hz
    · exact (F x).2
    · exact hconvex (ih hx) (ih hy) hr0.le (by linarith) (by ring)

theorem rfp_separable {C : Set X}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hbounded : Bornology.IsBounded C)
    (hconvex : Convex ℝ C) (F : C → C) (hF : LipschitzWith 1 F) :
    ∃ S : Set X, S ⊆ C ∧ S.Nonempty ∧ IsClosed S ∧ Bornology.IsBounded S ∧
      Convex ℝ S ∧ IsSeparable S ∧ InvariantSubset C F S := by
  obtain ⟨x0, hx0⟩ := hne
  set U := ⋃ n, rfpGen F x0 n
  have hUC : U ⊆ C := Set.iUnion_subset (fun n => rfpGen_sub hconvex F x0 hx0 n)
  have hSC : closure U ⊆ C := closure_minimal hUC hclosed
  -- closure of `U` under the operations
  have hUF : ∀ x : C, (x : X) ∈ U → (F x : X) ∈ U := by
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨n + 1, Or.inl (Or.inr ⟨x, hn, rfl⟩)⟩
  have hUcomb : ∀ r : ℚ, 0 < (r : ℝ) → (r : ℝ) < 1 → ∀ x ∈ U, ∀ y ∈ U,
      (r : ℝ) • x + (1 - (r : ℝ)) • y ∈ U := by
    intro r hr0 hr1 x hx y hy
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hy
    have hn' := rfpGen_mono F x0 (le_max_left n m) hn
    have hm' := rfpGen_mono F x0 (le_max_right n m) hm
    exact Set.mem_iUnion.mpr ⟨max n m + 1, Or.inr ⟨r, hr0, hr1, x, hn', y, hm', rfl⟩⟩
  refine ⟨closure U, hSC, ⟨x0, subset_closure (Set.mem_iUnion.mpr ⟨0, rfl⟩)⟩, isClosed_closure,
    hbounded.subset hSC, ?_, ?_, ?_⟩
  · -- convexity
    intro x hx y hy a b ha hb hab
    have hR : (Set.Icc (0 : ℝ) 1) ⊆ closure (Set.Ioo (0 : ℝ) 1 ∩ Set.range ((↑) : ℚ → ℝ)) := by
      rw [← closure_Ioo (zero_ne_one' ℝ)]
      exact closure_minimal (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo)
        isClosed_closure
    have ha' : a ∈ closure (Set.Ioo (0 : ℝ) 1 ∩ Set.range ((↑) : ℚ → ℝ)) :=
      hR ⟨ha, by linarith⟩
    have hxy : (x, y) ∈ closure (U ×ˢ U) := by
      rw [closure_prod_eq]; exact ⟨hx, hy⟩
    have hb' : b = 1 - a := by linarith
    subst hb'
    have := map_mem_closure₂ (f := fun (t : ℝ) (p : X × X) => t • p.1 + (1 - t) • p.2)
      (u := U) (by fun_prop) ha' hxy (by
        rintro t ⟨⟨ht0, ht1⟩, r, rfl⟩ p ⟨hp1, hp2⟩
        exact hUcomb r ht0 ht1 p.1 hp1 p.2 hp2)
    simpa using this
  · exact ((Set.countable_iUnion (fun n => rfpGen_countable F x0 n)).isSeparable).closure
  · -- invariance
    intro x hx
    have hcont : Continuous (fun x : C => (F x : X)) :=
      continuous_subtype_val.comp hF.continuous
    have hx' : x ∈ closure ((↑) ⁻¹' U : Set C) := by
      rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
        Set.image_preimage_eq_inter_range, Subtype.range_coe, Set.inter_eq_left.mpr hUC]
      exact hx
    exact map_mem_closure (f := fun x : C => (F x : X)) (t := U) hcont hx' (fun y hy => hUF y hy)

theorem solution
    (hX : CanonicallyReflexive X) {C : Set X}
    (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hconvex : Convex ℝ C)
    (F : C → C) (hF : LipschitzWith 1 F) (hno : ∀ x : C, F x ≠ x) :
    ∃ D : MinimalInvariantData (X := X), D.K ⊆ C := by
  let 𝒮 : Set (Set X) := {S | S ⊆ C ∧ S.Nonempty ∧ IsClosed S ∧ Convex ℝ S ∧ InvariantSubset C F S}
  have hC𝒮 : C ∈ 𝒮 := ⟨le_rfl, hne, hclosed, hconvex, fun x _ => (F x).2⟩
  obtain ⟨K, -, hKmin⟩ := zorn_superset_nonempty 𝒮 (fun c hc𝒮 hchain hcne => by
    refine ⟨⋂₀ c, ⟨?_, ?_, ?_, ?_, ?_⟩, fun s hs => Set.sInter_subset_of_mem hs⟩
    · obtain ⟨s, hs⟩ := hcne
      exact (Set.sInter_subset_of_mem hs).trans (hc𝒮 hs).1
    · refine rfp_chain hcne hchain (fun s hs => ?_) (fun s hs => ?_) (fun s hs => (hc𝒮 hs).2.1)
      · exact weaklyCompact_of_closed_bounded_convex hX (hc𝒮 hs).2.2.1
          (hbounded.subset (hc𝒮 hs).1) (hc𝒮 hs).2.2.2.1
      · exact weaklyClosed_of_closed_convex (hc𝒮 hs).2.2.1 (hc𝒮 hs).2.2.2.1
    · exact isClosed_sInter (fun s hs => (hc𝒮 hs).2.2.1)
    · exact convex_sInter (fun s hs => (hc𝒮 hs).2.2.2.1)
    · intro x hx
      rw [Set.mem_sInter] at hx ⊢
      exact fun s hs => (hc𝒮 hs).2.2.2.2 x (hx s hs)) C hC𝒮
  obtain ⟨hKC, hKne, hKcl, hKcv, hKinv⟩ := hKmin.prop
  -- the restricted map
  let T : K → K := fun x => ⟨F ⟨x, hKC x.2⟩, hKinv ⟨x, hKC x.2⟩ x.2⟩
  have hT : LipschitzWith 1 T := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    have := hF.dist_le_mul ⟨x, hKC x.2⟩ ⟨y, hKC y.2⟩
    simpa [T, Subtype.dist_eq] using this
  have hinvK : ∀ s : Set X, s ⊆ K → (InvariantSubset K T s ↔ InvariantSubset C F s) := by
    intro s hs
    constructor
    · intro h x hx
      exact h ⟨x, hs hx⟩ hx
    · intro h x hx
      exact h ⟨x, hKC x.2⟩ hx
  have hmin : MinimalInvariant K T := by
    intro s hsK hsne hscl hscv hsinv
    have hs𝒮 : s ∈ 𝒮 := ⟨hsK.trans hKC, hsne, hscl, hscv, (hinvK s hsK).1 hsinv⟩
    exact le_antisymm hsK (hKmin.2 hs𝒮 hsK)
  obtain ⟨S, hSK, hSne, hScl, -, hScv, hSsep, hSinv⟩ :=
    rfp_separable hKne hKcl (hbounded.subset hKC) hKcv T hT
  have hSeq : S = K := hmin S hSK hSne hScl hScv hSinv
  have hnf : ∀ x : K, T x ≠ x := by
    intro x hx
    apply hno ⟨x, hKC x.2⟩
    have := congrArg Subtype.val hx
    exact Subtype.ext this
  exact ⟨MinimalInvariantData.mk K hKne hKcl (hbounded.subset hKC) hKcv (hSeq ▸ hSsep)
    (weaklyCompact_of_closed_bounded_convex hX hKcl (hbounded.subset hKC) hKcv) T hT hnf hmin, hKC⟩
