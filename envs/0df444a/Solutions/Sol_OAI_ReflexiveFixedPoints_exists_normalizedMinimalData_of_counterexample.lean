-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.exists_normalizedMinimalData_of_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:02:30.612651+00:00
-- url     : https://prove2.me/submissions/9b23853c-90a9-430c-a4aa-b35a7ec26cfb

import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness
import Definitions.Def_OAI_Analysis_Nonexpansive_ScalarNormalization
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakMetric

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

theorem rfp_mid
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

theorem rfp_sep {K : Set X} (z : ℕ → K)
    (hz : DenseRange z) :
    Function.Injective (fun a : K => fun ij => pairNormingFunctional z ij a) := by
  intro a b hab
  by_contra hne
  have hδ : 0 < ‖(a : X) - b‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact fun h => hne (Subtype.ext h)
  set δ := ‖(a : X) - b‖
  obtain ⟨i, hi⟩ := hz.exists_dist_lt a (show 0 < δ / 5 by positivity)
  obtain ⟨j, hj⟩ := hz.exists_dist_lt b (show 0 < δ / 5 by positivity)
  rw [Subtype.dist_eq, dist_eq_norm] at hi hj
  have hspec := Classical.choose_spec (exists_dual_vector'' ℝ ((z i : X) - (z j : X)))
  set f := pairNormingFunctional z (i, j)
  have hf1 : ‖f‖ ≤ 1 := hspec.1
  have hf2 : f ((z i : X) - (z j : X)) = ‖(z i : X) - (z j : X)‖ := hspec.2
  have heq : f (a : X) = f (b : X) := congrFun hab (i, j)
  have hdiff : ‖(z i : X) - (z j : X)‖ ≥ 3 * δ / 5 := by
    have : δ ≤ ‖(a : X) - z i‖ + ‖(z i : X) - z j‖ + ‖(z j : X) - b‖ := by
      calc δ = ‖((a : X) - z i) + ((z i : X) - z j) + ((z j : X) - b)‖ := by rw [show ((a : X) - z i) + ((z i : X) - z j) + ((z j : X) - b) = (a : X) - b by abel]
        _ ≤ _ := norm_add₃_le
    have h1 : ‖(z j : X) - b‖ = ‖(b : X) - z j‖ := norm_sub_rev _ _
    linarith
  have herr : |f (((a : X) - z i) - ((b : X) - z j))| ≤ 2 * δ / 5 := by
    have := f.le_opNorm (((a : X) - z i) - ((b : X) - z j))
    have h2 : ‖((a : X) - z i) - ((b : X) - z j)‖ ≤ ‖(a : X) - z i‖ + ‖(b : X) - z j‖ := norm_sub_le _ _
    have h3 : ‖f‖ * ‖((a : X) - z i) - ((b : X) - z j)‖ ≤ 1 * (2 * δ / 5) :=
      mul_le_mul hf1 (by linarith) (norm_nonneg _) zero_le_one
    rw [← Real.norm_eq_abs]; linarith
  have hsplit : f (((a : X) - z i) - ((b : X) - z j)) = -f ((z i : X) - (z j : X)) := by
    have : ((a : X) - z i) - ((b : X) - z j) = ((a : X) - b) - ((z i : X) - z j) := by abel
    rw [this, map_sub, map_sub f (a : X), heq, sub_self, zero_sub]
  rw [hsplit, abs_neg, hf2, abs_of_nonneg (norm_nonneg _)] at herr
  linarith

theorem rfp_metr {K : Set X} (hsep : IsSeparable K)
    (hcompact : WeaklyCompact K) : MetrizableSpace (WeakCarrier K) := by
  rcases K.eq_empty_or_nonempty with hK | hK
  · subst hK
    haveI : IsEmpty (WeakCarrier (∅ : Set X)) := ⟨fun x => x.2⟩
    infer_instance
  haveI : Nonempty K := hK.to_subtype
  haveI : SeparableSpace K := hsep.separableSpace
  obtain ⟨z, hz⟩ := TopologicalSpace.exists_dense_seq K
  haveI : CompactSpace (WeakCarrier K) := hcompact.compactSpace
  let Φ : WeakCarrier K → (ℕ × ℕ → ℝ) := fun a ij =>
    pairNormingFunctional z ij ((toWeakSpace ℝ X).symm a.1)
  have hcont : Continuous Φ := by
    refine continuous_pi (fun ij => ?_)
    exact (WeakBilin.eval_continuous (topDualPairing ℝ X).flip (pairNormingFunctional z ij)).comp
      continuous_subtype_val
  have hinj : Function.Injective Φ := by
    intro a b hab
    have := rfp_sep z hz (a₁ := (normToWeak K).symm a) (a₂ := (normToWeak K).symm b) hab
    exact (normToWeak K).symm.injective this
  exact (hcont.isClosedEmbedding hinj).isEmbedding.metrizableSpace

open scoped Pointwise in
theorem solution
    (hX : CanonicallyReflexive X) {C : Set X}
    (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hconvex : Convex ℝ C)
    (F : C → C) (hF : LipschitzWith 1 F) (hno : ∀ x : C, F x ≠ x) :
    Nonempty (NormalizedMinimalData (X := X)) := by
  obtain ⟨D0, -⟩ := rfp_mid hX hne hclosed hbounded hconvex F hF hno
  have hd := D0.diam_pos
  set c := (Metric.diam D0.K)⁻¹
  have hc : 0 < c := inv_pos.mpr hd
  let D := D0.scaled hX c hc
  have hdiam : Metric.diam D.K = 1 := by
    change Metric.diam (c • D0.K) = 1
    rw [diam_smul₀, Real.norm_eq_abs, abs_of_pos hc, inv_mul_cancel₀ hd.ne']
  haveI : Nonempty D.K := D.nonempty.to_subtype
  haveI : SeparableSpace D.K := D.separable.separableSpace
  obtain ⟨z, hz⟩ := TopologicalSpace.exists_dense_seq D.K
  have hball : WeaklyCompact (differenceBall D.K) := by
    apply weaklyCompact_of_closed_bounded_convex hX
    · have h1 : IsClosed ((differenceSpan D.K : Set X)) :=
        Submodule.isClosed_topologicalClosure _
      have h2 : IsClosed {x : X | ‖x‖ ≤ 1} := isClosed_le continuous_norm continuous_const
      exact h1.inter h2
    · exact (Metric.isBounded_closedBall (x := (0 : X)) (r := 1)).subset
        (fun x hx => by simpa using hx.2)
    · intro x hx y hy a b ha hb hab
      refine ⟨(differenceSpan D.K).convex hx.1 hy.1 ha hb hab, ?_⟩
      calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
        _ = a * ‖x‖ + b * ‖y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
            abs_of_nonneg hb]
        _ ≤ a * 1 + b * 1 := by
          gcongr
          · exact hx.2
          · exact hy.2
        _ = 1 := by rw [mul_one, mul_one, hab]
  exact ⟨NormalizedMinimalData.mk D hdiam z hz (rfp_metr D.separable D.weak_compact) hball⟩
