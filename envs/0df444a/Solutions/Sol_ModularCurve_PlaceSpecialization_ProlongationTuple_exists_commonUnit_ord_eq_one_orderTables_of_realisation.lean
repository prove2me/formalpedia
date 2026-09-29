-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_commonUnit_ord_eq_one_orderTables_of_realisation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/2f56894a-1d2d-508d-9192-868d840af409

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_ord_eq_one_orderTables_of_realisation
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace MOVNCore

section Bookkeeping

variable {α β : Type*}

theorem mapDomain_apply_eq_sum [DecidableEq β] (E : α →₀ ℤ) (r : α → β) (v : β) :
    Finsupp.mapDomain r E v = ∑ W ∈ E.support, if r W = v then E W else 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finsupp.single_apply]

theorem mapDomain_nonneg (E : α →₀ ℤ) (r : α → β) (v : β)
    (h : ∀ W, r W = v → 0 ≤ E W) : 0 ≤ Finsupp.mapDomain r E v := by
  classical
  rw [mapDomain_apply_eq_sum]
  exact Finset.sum_nonneg fun W _ => by
    split_ifs with h'
    · exact h W h'
    · exact le_rfl

theorem le_mapDomain (E : α →₀ ℤ) (r : α → β) (v : β)
    (h : ∀ W, r W = v → 0 ≤ E W) {V : α} (hV : r V = v) :
    E V ≤ Finsupp.mapDomain r E v := by
  classical
  rw [mapDomain_apply_eq_sum]
  by_cases hs : V ∈ E.support
  · rw [← Finset.add_sum_erase _ _ hs, if_pos hV]
    refine le_add_of_nonneg_right (Finset.sum_nonneg fun W _ => ?_)
    split_ifs with h'
    · exact h W h'
    · exact le_rfl
  · rw [Finsupp.notMem_support_iff.mp hs]
    exact Finset.sum_nonneg fun W _ => by
      split_ifs with h'
      · exact h W h'
      · exact le_rfl

theorem add_le_mapDomain (E : α →₀ ℤ) (r : α → β) (v : β)
    (h : ∀ W, r W = v → 0 ≤ E W) {V V' : α} (hne : V ≠ V') (hV : r V = v) (hV' : r V' = v) :
    E V + E V' ≤ Finsupp.mapDomain r E v := by
  classical
  have hEV' : E V' = (E.erase V) V' := by rw [Finsupp.erase_ne (Ne.symm hne)]
  have herase : ∀ W, r W = v → 0 ≤ (E.erase V) W := by
    intro W hW
    by_cases hWV : W = V
    · rw [hWV, Finsupp.erase_same]
    · rw [Finsupp.erase_ne hWV]; exact h W hW
  have hsplit : Finsupp.mapDomain r E v = E V + Finsupp.mapDomain r (E.erase V) v := by
    conv_lhs => rw [← Finsupp.single_add_erase V E]
    rw [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
      if_pos hV]
  rw [hsplit, hEV']
  gcongr
  exact le_mapDomain (E.erase V) r v herase hV'

theorem mapDomain_filter_nonneg (D : α →₀ ℤ) (p : α → Prop) [DecidablePred p] (r : α → β) (v : β)
    (h : ∀ W, p W → r W = v → 0 ≤ D W) : 0 ≤ Finsupp.mapDomain r (D.filter p) v := by
  refine mapDomain_nonneg _ r v fun W hW => ?_
  rw [Finsupp.filter_apply]
  split_ifs with hp
  · exact h W hp hW
  · exact le_rfl

theorem le_mapDomain_filter (D : α →₀ ℤ) (p : α → Prop) [DecidablePred p] (r : α → β) (v : β)
    (h : ∀ W, p W → r W = v → 0 ≤ D W) {V : α} (hp : p V) (hV : r V = v) :
    D V ≤ Finsupp.mapDomain r (D.filter p) v := by
  have hDV : D V = (D.filter p) V := by rw [Finsupp.filter_apply, if_pos hp]
  rw [hDV]
  refine le_mapDomain _ r v (fun W hW => ?_) hV
  rw [Finsupp.filter_apply]
  split_ifs with hp'
  · exact h W hp' hW
  · exact le_rfl

theorem add_le_mapDomain_filter (D : α →₀ ℤ) (p : α → Prop) [DecidablePred p] (r : α → β) (v : β)
    (h : ∀ W, p W → r W = v → 0 ≤ D W) {V V' : α} (hne : V ≠ V')
    (hp : p V) (hV : r V = v) (hp' : p V') (hV' : r V' = v) :
    D V + D V' ≤ Finsupp.mapDomain r (D.filter p) v := by
  have hDV : D V = (D.filter p) V := by rw [Finsupp.filter_apply, if_pos hp]
  have hDV' : D V' = (D.filter p) V' := by rw [Finsupp.filter_apply, if_pos hp']
  rw [hDV, hDV']
  refine add_le_mapDomain _ r v (fun W hW => ?_) hne hV hV'
  rw [Finsupp.filter_apply]
  split_ifs with hp''
  · exact h W hp'' hW
  · exact le_rfl

theorem mapDomain_eq_zero_of_forall_ne (E : α →₀ ℤ) (r : α → β) (v : β)
    (h : ∀ W, E W ≠ 0 → r W ≠ v) : Finsupp.mapDomain r E v = 0 := by
  classical
  rw [mapDomain_apply_eq_sum]
  exact Finset.sum_eq_zero fun W hW => if_neg (h W (Finsupp.mem_support_iff.mp hW))

theorem sum_single_apply {ι : Type*} [Fintype ι] (Q : ι → α) (W : α) [DecidableEq α] :
    (∑ i, Finsupp.single (Q i) (1 : ℤ)) W = ∑ i, if Q i = W then (1 : ℤ) else 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.single_apply]

theorem sum_single_apply_nonneg {ι : Type*} [Fintype ι] (Q : ι → α) (W : α) :
    0 ≤ (∑ i, Finsupp.single (Q i) (1 : ℤ)) W := by
  classical
  rw [sum_single_apply]
  exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num

theorem sum_single_apply_eq_zero {ι : Type*} [Fintype ι] (Q : ι → α) (W : α) (h : ∀ i, Q i ≠ W) :
    (∑ i, Finsupp.single (Q i) (1 : ℤ)) W = 0 := by
  classical
  rw [sum_single_apply]
  exact Finset.sum_eq_zero fun i _ => if_neg (h i)

theorem exists_of_sum_single_apply_ne_zero {ι : Type*} [Fintype ι] (Q : ι → α) (W : α)
    (h : (∑ i, Finsupp.single (Q i) (1 : ℤ)) W ≠ 0) : ∃ i, Q i = W := by
  by_contra hne
  push Not at hne
  exact h (sum_single_apply_eq_zero Q W hne)

end Bookkeeping

section PlaceValues

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem HasValue.sub {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨sub_mem hg hg', ?_⟩
  have hx : (⟨g - g', sub_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ - ⟨g', hg'⟩ := rfl
  rw [hx, map_sub, hr, hr', map_sub]

theorem HasValue.sub_const {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) (b : K) :
    v.HasValue (g - algebraMap K F b) (a - b) :=
  HasValue.sub h (v.hasValue_algebraMap b)

theorem ord_pos_of_hasValue_zero (v : Place K F) {g : F} (hg : g ≠ 0) (h : v.HasValue g 0) :
    0 < v.ord g := by
  have hmem := h.mem
  have hres : IsLocalRing.residue v.toValuationSubring ⟨g, hmem⟩ = 0 := by
    rw [h.residue_eq, map_zero]
  have hmax : (⟨g, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
    (IsLocalRing.residue_eq_zero_iff _).mp hres
  have h0 : 0 ≤ v.ord g := v.ord_nonneg_of_mem hmem
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hg heq.symm
    exact (IsLocalRing.mem_maximalIdeal _).mp hmax hu

theorem hasValue_of_ord_sub_pos (v : Place K F) {g : F} {b : K}
    (h : 0 < v.ord (g - algebraMap K F b)) : v.HasValue g b := by
  have hne : g - algebraMap K F b ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h
  have hmem : g - algebraMap K F b ∈ v.toValuationSubring := v.mem_of_ord_nonneg hne h.le
  have hmax : (⟨_, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    change v.ord (g - algebraMap K F b) = 0 at h0
    omega
  have hgmem : g ∈ v.toValuationSubring := by
    have : g = (g - algebraMap K F b) + algebraMap K F b := by ring
    rw [this]
    exact add_mem hmem (v.algebraMap_mem' b)
  refine ⟨hgmem, ?_⟩
  have hx : (⟨g, hgmem⟩ : v.toValuationSubring) =
      ⟨_, hmem⟩ + ⟨algebraMap K F b, v.algebraMap_mem' b⟩ := Subtype.ext (by push_cast; ring)
  rw [hx, map_add, (IsLocalRing.residue_eq_zero_iff _).mpr hmax, zero_add]
  exact v.residue_algebraMap b

theorem ord_sub_eq_zero_of_hasValue_ne (v : Place K F) {g : F} {a b : K}
    (h : v.HasValue g a) (hab : a ≠ b) : v.ord (g - algebraMap K F b) = 0 :=
  (HasValue.sub_const h b).ord_eq_zero (sub_ne_zero.mpr hab)

theorem ord_sub_pos_of_hasValue (v : Place K F) {g : F} {b : K}
    (h : v.HasValue g b) (hne : g - algebraMap K F b ≠ 0) : 0 < v.ord (g - algebraMap K F b) := by
  have h' := HasValue.sub_const h b
  rw [sub_self] at h'
  exact ord_pos_of_hasValue_zero v hne h'

theorem eq_of_ord_sub_pos_of_hasValue (v : Place K F) {g : F} {a b : K}
    (ha : v.HasValue g a) (h : 0 < v.ord (g - algebraMap K F b)) : b = a :=
  (hasValue_of_ord_sub_pos v h).unique ha

theorem ord_sub_const_nonneg (v : Place K F) {g : F} (hg : g = 0 ∨ 0 ≤ v.ord g) (b : K) :
    0 ≤ v.ord (g - algebraMap K F b) := by
  have hmem : g ∈ v.toValuationSubring := by
    rcases hg with rfl | hg
    · exact zero_mem _
    · by_cases h0 : g = 0
      · rw [h0]; exact zero_mem _
      · exact v.mem_of_ord_nonneg h0 hg
  exact v.ord_nonneg_of_mem (sub_mem hmem (v.algebraMap_mem' b))

theorem ord_nonneg_of_mem_riemannRochSpace {D : Divisor K F} {g : F} (hg : g ∈ riemannRochSpace D)
    (v : Place K F) (hv : D v = 0) : g = 0 ∨ 0 ≤ v.ord g := by
  have h := (mem_riemannRochSpace_iff.mp hg) v
  rw [hv, neg_zero] at h
  exact h

theorem riemannRochSpace_mono {D D' : Divisor K F} (h : ∀ v, D v ≤ D' v) :
    riemannRochSpace D ≤ riemannRochSpace D' := by
  intro g hg
  rw [mem_riemannRochSpace_iff] at hg ⊢
  intro v
  rcases hg v with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (le_trans (neg_le_neg (h v)) h1)

theorem ord_neg_of_ord_sub_const_neg (v : Place K F) {g : F} {b : K}
    (h : v.ord (g - algebraMap K F b) < 0) : g ≠ 0 ∧ v.ord g < 0 := by
  by_contra hc
  have : g = 0 ∨ 0 ≤ v.ord g := by
    by_cases h0 : g = 0
    · exact Or.inl h0
    · exact Or.inr (not_lt.mp fun hlt => hc ⟨h0, hlt⟩)
  exact absurd (ord_sub_const_nonneg v this b) (not_le.mpr h)

theorem surjective_algebraMap_residueField [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

theorem exists_hasValue_of_ord_nonneg [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) {g : F}
    (hg : g = 0 ∨ 0 ≤ v.ord g) : ∃ a : K, v.HasValue g a := by
  have hmem : g ∈ v.toValuationSubring := by
    rcases hg with rfl | hg
    · exact zero_mem _
    · by_cases h0 : g = 0
      · rw [h0]; exact zero_mem _
      · exact v.mem_of_ord_nonneg h0 hg
  obtain ⟨a, ha, -⟩ := v.exists_hasValue_of_surjective (surjective_algebraMap_residueField v) hmem
  exact ⟨a, ha⟩

theorem ord_const_mul (v : Place K F) {c : K} (hc : c ≠ 0) (g : F) :
    v.ord (algebraMap K F c * g) = v.ord g := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [mul_zero]
  · rw [v.ord_mul ((map_ne_zero _).mpr hc) hg]
    have hu : IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) :=
      (v.hasValue_algebraMap c).isUnit hc
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    change v.ord (algebraMap K F c) = 0 at h0
    rw [h0, zero_add]

theorem degree_sum_single [IsAlgClosed K] [IsCurveOver K F] {ι : Type*} [Fintype ι] (Q : ι → Place K F) :
    Divisor.degree (∑ i, Finsupp.single (Q i) (1 : ℤ)) = Fintype.card ι := by
  rw [map_sum]
  simp_rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed]
  simp

end PlaceValues

section GeometryN

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

set_option hygiene false in
local notation "φ" => frobOnPlacesGeomLevel k N data hKr

theorem trichotomy (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    P.IsStrictFst W ∨ P.IsStrictSnd W ∨
    (φ (φ (P.reduceFst W)) = P.reduceFst W ∧ P.reduceSnd W = φ (P.reduceFst W)) := by
  rcases P.d1 W with h | h
  ·
    change P.reduceFst W = φ (P.reduceSnd W) at h
    by_cases hfix : φ (φ (P.reduceSnd W)) = P.reduceSnd W
    · refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · rw [h, hfix]
      · rw [h, hfix]
    · exact Or.inr (Or.inl ⟨h, hfix⟩)
  · change φ (P.reduceFst W) = P.reduceSnd W at h
    by_cases hfix : φ (φ (P.reduceFst W)) = P.reduceFst W
    · exact Or.inr (Or.inr ⟨hfix, h.symm⟩)
    · exact Or.inl ⟨h, hfix⟩

variable {P}

theorem not_fixed_reduceFst_of_isStrictFst {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : P.IsStrictFst W) : φ (φ (P.reduceFst W)) ≠ P.reduceFst W := h.2

theorem not_fixed_reduceSnd_of_isStrictSnd {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : P.IsStrictSnd W) : φ (φ (P.reduceSnd W)) ≠ P.reduceSnd W := h.2

theorem not_fixed_reduceSnd_of_isStrictFst {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : P.IsStrictFst W) : φ (φ (P.reduceSnd W)) ≠ P.reduceSnd W := by
  intro hfix
  apply h.2
  have e : P.reduceSnd W = φ (P.reduceFst W) := h.1.symm
  rw [e] at hfix

  exact frobOnPlacesGeomLevel_injective k N data hKr hfix

theorem not_fixed_reduceFst_of_isStrictSnd {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : P.IsStrictSnd W) : φ (φ (P.reduceFst W)) ≠ P.reduceFst W := by
  intro hfix
  apply h.2
  have e : P.reduceFst W = φ (P.reduceSnd W) := h.1
  rw [e] at hfix
  exact frobOnPlacesGeomLevel_injective k N data hKr hfix

theorem not_isStrictSnd_of_isStrictFst {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h1 : P.IsStrictFst W) (h2 : P.IsStrictSnd W) : False := by

  apply h2.2
  have e1 : φ (P.reduceFst W) = P.reduceSnd W := h1.1
  have e2 : P.reduceFst W = φ (P.reduceSnd W) := h2.1
  rw [e2] at e1
  exact e1

end GeometryN

section CountN

theorem ord_algebraMap_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) :
    v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, Place.ord_zero]
  · exact (v.hasValue_algebraMap c).ord_eq_zero hc

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

set_option hygiene false in
local notation "φ" => frobOnPlacesGeomLevel k N data hKr
set_option hygiene false in
local notation "F" => ↥(modularFunctionFieldBar (N * q))
set_option hygiene false in
local notation "Ck" => ↥(modularFunctionFieldC k N)

variable (P : PlaceSpecialization A q N data hKr k red hα hβ)

theorem kind
    (hcusp : ∀ V : Place (AlgebraicClosure ℚ) F, ¬ IsAffineGeomPlace k N (P.reduceFst V) → ProlongationTuple.IsCuspidal P V)
    (hsplit : ∀ V : Place (AlgebraicClosure ℚ) F, ProlongationTuple.IsCuspidal P V →
      ProlongationTuple.IsInftySide P V ∨ ProlongationTuple.IsZeroSide P V)
    (V : Place (AlgebraicClosure ℚ) F) :
    P.IsStrictFst V ∨ P.IsStrictSnd V ∨
    (φ (φ (P.reduceFst V)) = P.reduceFst V ∧ IsAffineGeomPlace k N (P.reduceFst V) ∧ P.reduceSnd V = φ (P.reduceFst V)) ∨
    (ProlongationTuple.IsInftySide P V ∧ φ (φ (P.reduceFst V)) = P.reduceFst V ∧ P.reduceSnd V = φ (P.reduceFst V)) ∨
    (ProlongationTuple.IsZeroSide P V ∧ φ (φ (P.reduceFst V)) = P.reduceFst V ∧ P.reduceSnd V = φ (P.reduceFst V)) := by
  rcases trichotomy P V with h | h | ⟨hfix, hsnd⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · by_cases haff : IsAffineGeomPlace k N (P.reduceFst V)
    · exact Or.inr (Or.inr (Or.inl ⟨hfix, haff, hsnd⟩))
    · rcases hsplit V (hcusp V haff) with hs | hs
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hs, hfix, hsnd⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hs, hfix, hsnd⟩)))

variable {P}

variable {D : Divisor (AlgebraicClosure ℚ) F} {Z : Set (Place k Ck)}

theorem nonneg_fst_fibre
    (hDpole : ∀ W, D W < 0 → (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z))
    {v : Place k Ck} (hv : v ∈ Z) :
    ∀ W, P.IsStrictFst W → P.reduceFst W = v → 0 ≤ D W := by
  intro W h1 hW
  by_contra hlt
  push Not at hlt
  rcases hDpole W hlt with ⟨-, hZ⟩ | ⟨h2, -⟩
  · exact hZ (by rw [hW]; exact hv)
  · exact not_isStrictSnd_of_isStrictFst h1 h2

theorem nonneg_snd_fibre
    (hDpole : ∀ W, D W < 0 → (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z))
    {v : Place k Ck} (hv : v ∈ Z) :
    ∀ W, P.IsStrictSnd W → P.reduceSnd W = v → 0 ≤ D W := by
  intro W h2 hW
  by_contra hlt
  push Not at hlt
  rcases hDpole W hlt with ⟨h1, -⟩ | ⟨-, hZ⟩
  · exact not_isStrictSnd_of_isStrictFst h1 h2
  · exact hZ (by rw [hW]; exact hv)

theorem nonneg_fixed_fibre
    (hDpole : ∀ W, D W < 0 → (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z))
    {v : Place k Ck} (hv : φ (φ v) = v) :
    ∀ W, P.reduceFst W = v → 0 ≤ D W := by
  intro W hW
  by_contra hlt
  push Not at hlt
  rcases hDpole W hlt with ⟨h1, -⟩ | ⟨h2, -⟩
  · exact not_fixed_reduceFst_of_isStrictFst h1 (by rw [hW]; exact hv)
  · exact not_fixed_reduceFst_of_isStrictSnd h2 (by rw [hW]; exact hv)

theorem nonneg_infty_fibre
    (hDpole : ∀ W, D W < 0 → (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z))
    (hZcusp : ∀ W, ProlongationTuple.IsInftySide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z)
    (c : Place (AlgebraicClosure ℚ) F) :
    ∀ W, ProlongationTuple.IsInftySide P W → P.reduceFst W = P.reduceFst c → 0 ≤ D W := by
  intro W hW _
  by_contra hlt
  push Not at hlt
  rcases hDpole W hlt with ⟨-, hZ⟩ | ⟨-, hZ⟩
  · exact hZ (hZcusp W hW).1
  · exact hZ (hZcusp W hW).2

theorem nonneg_zero_fibre
    (hDpole : ∀ W, D W < 0 → (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z))
    (hZcusp' : ∀ W, ProlongationTuple.IsZeroSide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z)
    (c : Place (AlgebraicClosure ℚ) F) :
    ∀ W, ProlongationTuple.IsZeroSide P W → P.reduceSnd W = P.reduceSnd c → 0 ≤ D W := by
  intro W hW _
  by_contra hlt
  push Not at hlt
  rcases hDpole W hlt with ⟨-, hZ⟩ | ⟨-, hZ⟩
  · exact hZ (hZcusp' W hW).1
  · exact hZ (hZcusp' W hW).2

theorem rawResidue₁_ne_zero (R : ProlongationTuple P) {x : R.R₁.integers} (h : R.residue₁ x ≠ 0) :
    R.R₁.residue x ≠ 0 := by
  intro h0; apply h; rw [ProlongationTuple.residue₁_apply, h0, map_zero]

theorem rawResidue₂_ne_zero (R : ProlongationTuple P) {x : R.R₂.integers} (h : R.residue₂ x ≠ 0) :
    R.R₂.residue x ≠ 0 := by
  intro h0; apply h; rw [ProlongationTuple.residue₂_apply, h0, map_zero]

theorem classBound (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (hcusp : ∀ V : Place (AlgebraicClosure ℚ) F, ¬ IsAffineGeomPlace k N (P.reduceFst V) → ProlongationTuple.IsCuspidal P V)
    (hsplit : ∀ V : Place (AlgebraicClosure ℚ) F, ProlongationTuple.IsCuspidal P V →
      ProlongationTuple.IsInftySide P V ∨ ProlongationTuple.IsZeroSide P V)
    (f : F) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hf₁ : R.residue₁ ⟨f, h₁⟩ ≠ 0) (hf₂ : R.residue₂ ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) F) (hD : ∀ W, D W = W.ord f)
    (Z : Set (Place k Ck))
    (hDpole : ∀ W, D W < 0 → (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z))
    (hZcusp : ∀ W, ProlongationTuple.IsInftySide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z)
    (hZcusp' : ∀ W, ProlongationTuple.IsZeroSide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z)
    (V : Place (AlgebraicClosure ℚ) F) (hz₁ : P.reduceFst V ∈ Z) (hz₂ : P.reduceSnd V ∈ Z) :
    (P.IsStrictFst V ∧
      D V ≤ (P.reduceFst V).ord (R.residue₁ ⟨f, h₁⟩) ∧
      ∀ V', V' ≠ V → P.IsStrictFst V' → P.reduceFst V' = P.reduceFst V →
        D V + D V' ≤ (P.reduceFst V).ord (R.residue₁ ⟨f, h₁⟩)) ∨
    (P.IsStrictSnd V ∧
      D V ≤ (P.reduceSnd V).ord (R.residue₂ ⟨f, h₂⟩) ∧
      ∀ V', V' ≠ V → P.IsStrictSnd V' → P.reduceSnd V' = P.reduceSnd V →
        D V + D V' ≤ (P.reduceSnd V).ord (R.residue₂ ⟨f, h₂⟩)) ∨
    ((φ (φ (P.reduceFst V)) = P.reduceFst V ∧ IsAffineGeomPlace k N (P.reduceFst V) ∧ P.reduceSnd V = φ (P.reduceFst V)) ∧
      D V ≤ (P.reduceFst V).ord (R.residue₁ ⟨f, h₁⟩) + (P.reduceSnd V).ord (R.residue₂ ⟨f, h₂⟩) ∧
      ∀ V', V' ≠ V → P.reduceFst V' = P.reduceFst V →
        D V + D V' ≤ (P.reduceFst V).ord (R.residue₁ ⟨f, h₁⟩) + (P.reduceSnd V).ord (R.residue₂ ⟨f, h₂⟩)) ∨
    ((ProlongationTuple.IsInftySide P V ∧ φ (φ (P.reduceFst V)) = P.reduceFst V ∧ P.reduceSnd V = φ (P.reduceFst V)) ∧
      D V ≤ (P.reduceFst V).ord (R.residue₁ ⟨f, h₁⟩) ∧
      ∀ V', V' ≠ V → ProlongationTuple.IsInftySide P V' → P.reduceFst V' = P.reduceFst V →
        D V + D V' ≤ (P.reduceFst V).ord (R.residue₁ ⟨f, h₁⟩)) ∨
    ((ProlongationTuple.IsZeroSide P V ∧ φ (φ (P.reduceFst V)) = P.reduceFst V ∧ P.reduceSnd V = φ (P.reduceFst V)) ∧
      D V ≤ (P.reduceSnd V).ord (R.residue₂ ⟨f, h₂⟩) ∧
      ∀ V', V' ≠ V → ProlongationTuple.IsZeroSide P V' → P.reduceSnd V' = P.reduceSnd V →
        D V + D V' ≤ (P.reduceSnd V).ord (R.residue₂ ⟨f, h₂⟩)) := by
  classical
  obtain ⟨hDF, hDS, hCI, hCZ⟩ : R.DivisorLawFst ∧ R.DivisorLawSnd ∧ R.CuspLawInfty ∧ R.CuspLawZero := hR
  have hf₁' : R.R₁.residue ⟨f, h₁⟩ ≠ 0 := rawResidue₁_ne_zero R hf₁
  have hf₂' : R.R₂.residue ⟨f, h₂⟩ ≠ 0 := rawResidue₂_ne_zero R hf₂
  rcases kind P hcusp hsplit V with hk | hk | hk | hk | hk
  · have hlaw := hDF f h₁ h₂ hf₁' hf₂' D hD (P.reduceFst V) hk.2
    refine Or.inl ⟨hk, ?_, ?_⟩
    · rw [← hlaw]
      exact le_mapDomain_filter D P.IsStrictFst P.reduceFst _ (nonneg_fst_fibre hDpole hz₁) hk rfl
    · intro V' hne h1' hV'
      rw [← hlaw]
      exact add_le_mapDomain_filter D P.IsStrictFst P.reduceFst _
        (nonneg_fst_fibre hDpole hz₁) (Ne.symm hne) hk rfl h1' hV'
  · have hlaw := hDS f h₁ h₂ hf₁' hf₂' D hD (P.reduceSnd V) hk.2
    refine Or.inr (Or.inl ⟨hk, ?_, ?_⟩)
    · rw [← hlaw]
      exact le_mapDomain_filter D P.IsStrictSnd P.reduceSnd _ (nonneg_snd_fibre hDpole hz₂) hk rfl
    · intro V' hne h2' hV'
      rw [← hlaw]
      exact add_le_mapDomain_filter D P.IsStrictSnd P.reduceSnd _
        (nonneg_snd_fibre hDpole hz₂) (Ne.symm hne) hk rfl h2' hV'
  · obtain ⟨hfix, haff, hsnd⟩ := hk
    have hlaw := hO f h₁ h₂ hf₁' hf₂' D hD (P.reduceFst V) hfix haff
    refine Or.inr (Or.inr (Or.inl ⟨⟨hfix, haff, hsnd⟩, ?_, ?_⟩))
    · rw [hsnd, ← hlaw]
      exact le_mapDomain D P.reduceFst _ (nonneg_fixed_fibre hDpole hfix) rfl
    · intro V' hne hV'
      rw [hsnd, ← hlaw]
      exact add_le_mapDomain D P.reduceFst _ (nonneg_fixed_fibre hDpole hfix) (Ne.symm hne) rfl hV'
  · have hlaw := hCI f h₁ h₂ hf₁' hf₂' D hD V hk.1
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hk, ?_, ?_⟩)))
    · rw [← hlaw]
      exact le_mapDomain_filter D (ProlongationTuple.IsInftySide P) P.reduceFst _
        (nonneg_infty_fibre hDpole hZcusp V) hk.1 rfl
    · intro V' hne hs' hV'
      rw [← hlaw]
      exact add_le_mapDomain_filter D (ProlongationTuple.IsInftySide P) P.reduceFst _
        (nonneg_infty_fibre hDpole hZcusp V) (Ne.symm hne) hk.1 rfl hs' hV'
  · have hlaw := hCZ f h₁ h₂ hf₁' hf₂' D hD V hk.1
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hk, ?_, ?_⟩)))
    · rw [← hlaw]
      exact le_mapDomain_filter D (ProlongationTuple.IsZeroSide P) P.reduceSnd _
        (nonneg_zero_fibre hDpole hZcusp' V) hk.1 rfl
    · intro V' hne hs' hV'
      rw [← hlaw]
      exact add_le_mapDomain_filter D (ProlongationTuple.IsZeroSide P) P.reduceSnd _
        (nonneg_zero_fibre hDpole hZcusp' V) (Ne.symm hne) hk.1 rfl hs' hV'

end CountN

section ZeroCountN

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

set_option hygiene false in
local notation "φ" => frobOnPlacesGeomLevel k N data hKr
set_option hygiene false in
local notation "F" => ↥(modularFunctionFieldBar (N * q))
set_option hygiene false in
local notation "Ck" => ↥(modularFunctionFieldC k N)

theorem one_le_ord_residue_or (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (hcusp : ∀ V : Place (AlgebraicClosure ℚ) F, ¬ IsAffineGeomPlace k N (P.reduceFst V) → ProlongationTuple.IsCuspidal P V)
    (hsplit : ∀ V : Place (AlgebraicClosure ℚ) F, ProlongationTuple.IsCuspidal P V →
      ProlongationTuple.IsInftySide P V ∨ ProlongationTuple.IsZeroSide P V)
    (f : F) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hf₁ : R.residue₁ ⟨f, h₁⟩ ≠ 0) (hf₂ : R.residue₂ ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) F) (hD : ∀ W, D W = W.ord f)
    (Z : Set (Place k Ck))
    (hDpole : ∀ W, D W < 0 → (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z))
    (hZcusp : ∀ W, ProlongationTuple.IsInftySide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z)
    (hZcusp' : ∀ W, ProlongationTuple.IsZeroSide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z)
    (V₀ : Place (AlgebraicClosure ℚ) F) (hDV₀ : 1 ≤ D V₀)
    (hd₁ : P.reduceFst V₀ ∈ Z) (hd₂ : P.reduceSnd V₀ ∈ Z)
    (hreg₁ : 0 ≤ (P.reduceFst V₀).ord (R.residue₁ ⟨f, h₁⟩))
    (hreg₂ : 0 ≤ (P.reduceSnd V₀).ord (R.residue₂ ⟨f, h₂⟩)) :
    1 ≤ (P.reduceFst V₀).ord (R.residue₁ ⟨f, h₁⟩) ∨ 1 ≤ (P.reduceSnd V₀).ord (R.residue₂ ⟨f, h₂⟩) := by
  rcases classBound R hR hO hcusp hsplit f h₁ h₂ hf₁ hf₂ D hD Z hDpole hZcusp hZcusp' V₀ hd₁ hd₂ with
    ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩
  · exact Or.inl (hDV₀.trans hb)
  · exact Or.inr (hDV₀.trans hb)
  · rcases le_or_gt 1 ((P.reduceFst V₀).ord (R.residue₁ ⟨f, h₁⟩)) with h | h
    · exact Or.inl h
    · right; omega
  · exact Or.inl (hDV₀.trans hb)
  · exact Or.inr (hDV₀.trans hb)

theorem eq_one_and_forall_of_orders (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (hcusp : ∀ V : Place (AlgebraicClosure ℚ) F, ¬ IsAffineGeomPlace k N (P.reduceFst V) → ProlongationTuple.IsCuspidal P V)
    (hsplit : ∀ V : Place (AlgebraicClosure ℚ) F, ProlongationTuple.IsCuspidal P V →
      ProlongationTuple.IsInftySide P V ∨ ProlongationTuple.IsZeroSide P V)
    (hInftyNA : ∀ V : Place (AlgebraicClosure ℚ) F, ProlongationTuple.IsInftySide P V → ¬ IsAffineGeomPlace k N (P.reduceFst V))
    (hZeroNA : ∀ V : Place (AlgebraicClosure ℚ) F, ProlongationTuple.IsZeroSide P V → ¬ IsAffineGeomPlace k N (P.reduceSnd V))
    (hφaff : ∀ v : Place k Ck, IsAffineGeomPlace k N v → IsAffineGeomPlace k N (φ v))
    (f : F) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hf₁ : R.residue₁ ⟨f, h₁⟩ ≠ 0) (hf₂ : R.residue₂ ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) F) (hD : ∀ W, D W = W.ord f)
    (Z : Set (Place k Ck))
    (hDpole : ∀ W, D W < 0 → (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z))
    (hZcusp : ∀ W, ProlongationTuple.IsInftySide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z)
    (hZcusp' : ∀ W, ProlongationTuple.IsZeroSide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z)
    (V₀ : Place (AlgebraicClosure ℚ) F) (hDV₀ : 1 ≤ D V₀)
    (hd₁ : P.reduceFst V₀ ∈ Z) (hd₂ : P.reduceSnd V₀ ∈ Z)
    (p₁ p₂ : Prop) (hp : ¬ (p₁ ∧ p₂))
    (hZ₁ : ∀ z ∈ Z, z ≠ P.reduceFst V₀ → z.ord (R.residue₁ ⟨f, h₁⟩) = 0)
    (hZ₂ : ∀ z ∈ Z, z ≠ P.reduceSnd V₀ → z.ord (R.residue₂ ⟨f, h₂⟩) = 0)
    (h1p : p₁ → (P.reduceFst V₀).ord (R.residue₁ ⟨f, h₁⟩) = 1)
    (h1n : ¬ p₁ → (P.reduceFst V₀).ord (R.residue₁ ⟨f, h₁⟩) = 0)
    (h2p : p₂ → (P.reduceSnd V₀).ord (R.residue₂ ⟨f, h₂⟩) = 1)
    (h2n : ¬ p₂ → (P.reduceSnd V₀).ord (R.residue₂ ⟨f, h₂⟩) = 0) :
    D V₀ = 1 ∧ ∀ V, V ≠ V₀ → 1 ≤ D V → P.reduceFst V ∈ Z → P.reduceSnd V ∈ Z → False := by
  classical
  have hφinj := ModularCurve.frobOnPlacesGeomLevel_injective k N data hKr
  have hA : ∀ z ∈ Z, 0 ≤ z.ord (R.residue₁ ⟨f, h₁⟩) ∧ z.ord (R.residue₁ ⟨f, h₁⟩) ≤ 1 ∧
      (1 ≤ z.ord (R.residue₁ ⟨f, h₁⟩) → z = P.reduceFst V₀ ∧ p₁) := by
    intro z hz
    by_cases hzd : z = P.reduceFst V₀
    · by_cases hq : p₁
      · rw [hzd, h1p hq]; exact ⟨by norm_num, le_rfl, fun _ => ⟨rfl, hq⟩⟩
      · rw [hzd, h1n hq]; exact ⟨le_rfl, by norm_num, fun h => absurd h (by norm_num)⟩
    · rw [hZ₁ z hz hzd]; exact ⟨le_rfl, by norm_num, fun h => absurd h (by norm_num)⟩
  have hB : ∀ z ∈ Z, 0 ≤ z.ord (R.residue₂ ⟨f, h₂⟩) ∧ z.ord (R.residue₂ ⟨f, h₂⟩) ≤ 1 ∧
      (1 ≤ z.ord (R.residue₂ ⟨f, h₂⟩) → z = P.reduceSnd V₀ ∧ p₂) := by
    intro z hz
    by_cases hzd : z = P.reduceSnd V₀
    · by_cases hq : p₂
      · rw [hzd, h2p hq]; exact ⟨by norm_num, le_rfl, fun _ => ⟨rfl, hq⟩⟩
      · rw [hzd, h2n hq]; exact ⟨le_rfl, by norm_num, fun h => absurd h (by norm_num)⟩
    · rw [hZ₂ z hz hzd]; exact ⟨le_rfl, by norm_num, fun h => absurd h (by norm_num)⟩

  have hloc : ∀ V, P.reduceFst V ∈ Z → P.reduceSnd V ∈ Z → 1 ≤ D V →
      (p₁ ∧ (
        (P.IsStrictFst V ∧ P.reduceFst V = P.reduceFst V₀ ∧
          ∀ V', V' ≠ V → P.IsStrictFst V' → P.reduceFst V' = P.reduceFst V → D V + D V' ≤ 1) ∨
        (φ (φ (P.reduceFst V)) = P.reduceFst V ∧ IsAffineGeomPlace k N (P.reduceFst V) ∧ P.reduceFst V = P.reduceFst V₀ ∧
          ∀ V', V' ≠ V → P.reduceFst V' = P.reduceFst V → D V + D V' ≤ 1) ∨
        (ProlongationTuple.IsInftySide P V ∧ φ (φ (P.reduceFst V)) = P.reduceFst V ∧ P.reduceFst V = P.reduceFst V₀ ∧
          ∀ V', V' ≠ V → ProlongationTuple.IsInftySide P V' → P.reduceFst V' = P.reduceFst V → D V + D V' ≤ 1))) ∨
      (p₂ ∧ (
        (P.IsStrictSnd V ∧ P.reduceSnd V = P.reduceSnd V₀ ∧
          ∀ V', V' ≠ V → P.IsStrictSnd V' → P.reduceSnd V' = P.reduceSnd V → D V + D V' ≤ 1) ∨
        (φ (φ (P.reduceFst V)) = P.reduceFst V ∧ IsAffineGeomPlace k N (P.reduceFst V) ∧ P.reduceSnd V = φ (P.reduceFst V) ∧ P.reduceSnd V = P.reduceSnd V₀ ∧
          ∀ V', V' ≠ V → P.reduceFst V' = P.reduceFst V → D V + D V' ≤ 1) ∨
        (ProlongationTuple.IsZeroSide P V ∧ φ (φ (P.reduceFst V)) = P.reduceFst V ∧ P.reduceSnd V = φ (P.reduceFst V) ∧ P.reduceSnd V = P.reduceSnd V₀ ∧
          ∀ V', V' ≠ V → ProlongationTuple.IsZeroSide P V' → P.reduceSnd V' = P.reduceSnd V → D V + D V' ≤ 1))) := by
    intro V hz₁ hz₂ hDV
    rcases classBound R hR hO hcusp hsplit f h₁ h₂ hf₁ hf₂ D hD Z hDpole hZcusp hZcusp' V hz₁ hz₂ with
      ⟨hk, hb, hb2⟩ | ⟨hk, hb, hb2⟩ | ⟨⟨hfix, haff, hsnd⟩, hb, hb2⟩ | ⟨⟨hk, hfix, hsnd⟩, hb, hb2⟩ |
      ⟨⟨hk, hfix, hsnd⟩, hb, hb2⟩
    · obtain ⟨ha0, ha1, ha⟩ := hA _ hz₁
      obtain ⟨hd, hq⟩ := ha (hDV.trans hb)
      exact Or.inl ⟨hq, Or.inl ⟨hk, hd, fun V' hne h1' hV' => (hb2 V' hne h1' hV').trans ha1⟩⟩
    · obtain ⟨hb0, hb1, hb'⟩ := hB _ hz₂
      obtain ⟨hd, hq⟩ := hb' (hDV.trans hb)
      exact Or.inr ⟨hq, Or.inl ⟨hk, hd, fun V' hne h2' hV' => (hb2 V' hne h2' hV').trans hb1⟩⟩
    · obtain ⟨ha0, ha1, ha⟩ := hA _ hz₁
      obtain ⟨hb0, hb1, hb'⟩ := hB _ hz₂
      rcases le_or_gt 1 ((P.reduceFst V).ord (R.residue₁ ⟨f, h₁⟩)) with hge | hlt
      · obtain ⟨hd, hq⟩ := ha hge
        refine Or.inl ⟨hq, Or.inr (Or.inl ⟨hfix, haff, hd, fun V' hne hV' => ?_⟩)⟩
        have := hb2 V' hne hV'
        have hb00 : (P.reduceSnd V).ord (R.residue₂ ⟨f, h₂⟩) = 0 := by
          rcases le_or_gt 1 ((P.reduceSnd V).ord (R.residue₂ ⟨f, h₂⟩)) with hge' | hlt'
          · exact absurd ⟨hq, (hb' hge').2⟩ hp
          · omega
        omega
      · have hge' : 1 ≤ (P.reduceSnd V).ord (R.residue₂ ⟨f, h₂⟩) := by omega
        obtain ⟨hd, hq⟩ := hb' hge'
        refine Or.inr ⟨hq, Or.inr (Or.inl ⟨hfix, haff, hsnd, hd, fun V' hne hV' => ?_⟩)⟩
        have := hb2 V' hne hV'
        omega
    · obtain ⟨ha0, ha1, ha⟩ := hA _ hz₁
      obtain ⟨hd, hq⟩ := ha (hDV.trans hb)
      exact Or.inl ⟨hq, Or.inr (Or.inr ⟨hk, hfix, hd, fun V' hne hs' hV' => (hb2 V' hne hs' hV').trans ha1⟩)⟩
    · obtain ⟨hb0, hb1, hb'⟩ := hB _ hz₂
      obtain ⟨hd, hq⟩ := hb' (hDV.trans hb)
      exact Or.inr ⟨hq, Or.inr (Or.inr ⟨hk, hfix, hsnd, hd, fun V' hne hs' hV' => (hb2 V' hne hs' hV').trans hb1⟩)⟩

  have hle : D V₀ ≤ 1 := by
    obtain ⟨ha0, ha1, ha⟩ := hA _ hd₁
    obtain ⟨hb0, hb1, hb'⟩ := hB _ hd₂
    rcases classBound R hR hO hcusp hsplit f h₁ h₂ hf₁ hf₂ D hD Z hDpole hZcusp hZcusp' V₀ hd₁ hd₂ with
      ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩
    · exact hb.trans ha1
    · exact hb.trans hb1
    · refine hb.trans ?_
      rcases le_or_gt 1 ((P.reduceFst V₀).ord (R.residue₁ ⟨f, h₁⟩)) with hge | hlt
      · rcases le_or_gt 1 ((P.reduceSnd V₀).ord (R.residue₂ ⟨f, h₂⟩)) with hge' | hlt'
        · exact absurd ⟨(ha hge).2, (hb' hge').2⟩ hp
        · omega
      · omega
    · exact hb.trans ha1
    · exact hb.trans hb1
  refine ⟨le_antisymm hle hDV₀, ?_⟩

  intro V hne hDV hz₁ hz₂
  have hV := hloc V hz₁ hz₂ hDV
  have hV₀ := hloc V₀ hd₁ hd₂ hDV₀
  rcases hV with ⟨hq, hV⟩ | ⟨hq, hV⟩ <;> rcases hV₀ with ⟨hq₀, hV₀⟩ | ⟨hq₀, hV₀⟩
  ·
    rcases hV with ⟨hk, hd, hbd⟩ | ⟨hfix, haff, hd, hbd⟩ | ⟨hk, hfix, hd, hbd⟩ <;>
      rcases hV₀ with ⟨hk₀, -, -⟩ | ⟨hfix₀, haff₀, -, -⟩ | ⟨hk₀, hfix₀, -, -⟩
    · have := hbd V₀ (Ne.symm hne) hk₀ hd.symm; omega
    · exact (hk.2 (by rw [hd]; exact hfix₀)).elim
    · exact (hk.2 (by rw [hd]; exact hfix₀)).elim
    · exact (hk₀.2 (by rw [← hd]; exact hfix)).elim
    · have := hbd V₀ (Ne.symm hne) hd.symm; omega
    · exact (hInftyNA V₀ hk₀ (by rw [← hd]; exact haff)).elim
    · exact (hk₀.2 (by rw [← hd]; exact hfix)).elim
    · exact (hInftyNA V hk (by rw [hd]; exact haff₀)).elim
    · have := hbd V₀ (Ne.symm hne) hk₀ hd.symm; omega
  · exact hp ⟨hq, hq₀⟩
  · exact hp ⟨hq₀, hq⟩
  ·
    rcases hV with ⟨hk, hd, hbd⟩ | ⟨hfix, haff, hsnd, hd, hbd⟩ | ⟨hk, hfix, hsnd, hd, hbd⟩ <;>
      rcases hV₀ with ⟨hk₀, -, -⟩ | ⟨hfix₀, haff₀, hsnd₀, -, -⟩ | ⟨hk₀, hfix₀, hsnd₀, -, -⟩
    · have := hbd V₀ (Ne.symm hne) hk₀ hd.symm; omega
    ·
      apply (hk.2 _).elim
      rw [hd, hsnd₀, hfix₀]
    · apply (hk.2 _).elim
      rw [hd, hsnd₀, hfix₀]
    · apply (hk₀.2 _).elim
      rw [← hd, hsnd, hfix]
    ·
      have heq : P.reduceFst V₀ = P.reduceFst V := hφinj (by rw [← hsnd₀, ← hd, hsnd])
      have := hbd V₀ (Ne.symm hne) heq; omega
    ·
      exact (hZeroNA V₀ hk₀ (by rw [← hd, hsnd]; exact hφaff _ haff)).elim
    · apply (hk₀.2 _).elim
      rw [← hd, hsnd, hfix]
    · exact (hZeroNA V hk (by rw [hd, hsnd₀]; exact hφaff _ haff₀)).elim
    · have := hbd V₀ (Ne.symm hne) hk₀ hd.symm; omega

end ZeroCountN

section SeamN

theorem residue_inv_eq_zero_of_not_mem {A : ValuationSubring (AlgebraicClosure ℚ)} {c : AlgebraicClosure ℚ} (hc : c ∉ A) (hc' : c⁻¹ ∈ A) :
    IsLocalRing.residue A ⟨c⁻¹, hc'⟩ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  apply hc
  have hc0 : c ≠ 0 := fun h0 => hc (h0 ▸ A.zero_mem)
  have h1 : c⁻¹ * (w : AlgebraicClosure ℚ) = 1 := by
    have := congrArg Subtype.val hw
    simpa using this
  have : (w : AlgebraicClosure ℚ) = c := by
    calc (w : AlgebraicClosure ℚ) = c * (c⁻¹ * w) := by rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
      _ = c := by rw [h1, mul_one]
  rw [← this]
  exact w.2

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  [CharP (ResidueField A) q]
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ}
  (R : ProlongationTuple P)

theorem redBar_eq_id : R.redBar = RingHom.id (ResidueField A) := by
  refine RingHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  exact R.redBar_residue a

theorem coeffMap_id' (y : LaurentSeries (ResidueField A)) : coeffMap (RingHom.id (ResidueField A)) y = y := by
  ext n; rfl

theorem coe_ι (g : ↥(modularFunctionFieldFullC (ResidueField A) N)) :
    ((R.ι g : ↥(modularFunctionFieldC (ResidueField A) N)) : LaurentSeries (ResidueField A)) =
      (g : LaurentSeries (ResidueField A)) := by
  rw [R.ι_coe, redBar_eq_id, coeffMap_id']

theorem ι_algebraMap (c : ResidueField A) :
    R.ι (algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) N) c)
      = algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) c := by
  apply Subtype.ext
  rw [coe_ι]
  exact ((IsScalarTower.algebraMap_apply (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) N)
        (LaurentSeries (ResidueField A)) c).symm.trans
      (IsScalarTower.algebraMap_apply (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)
        (LaurentSeries (ResidueField A)) c))

theorem algebraMap_mem_integers₁ (a : A) :
    algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers :=
  (R.R₁.algebraMap_mem_iff a).mpr a.2

theorem algebraMap_mem_integers₂ (a : A) :
    algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers :=
  (R.R₂.algebraMap_mem_iff a).mpr a.2

theorem residue₁_algebraMap (a : A)
    (h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers) :
    R.residue₁ ⟨_, h⟩ =
      algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A a) := by
  rw [ProlongationTuple.residue₁_apply, ← ι_algebraMap R]
  congr 1
  exact R.R₁.residue_algebraMap a

theorem residue₂_algebraMap (a : A)
    (h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h⟩ =
      algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A a) := by
  rw [ProlongationTuple.residue₂_apply, ← ι_algebraMap R]
  congr 1
  exact R.R₂.residue_algebraMap a

theorem residue₁_sub_algebraMap (f : ↥(modularFunctionFieldBar (N * q))) (h : f ∈ R.R₁.integers) (a : A)
    (h' : f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers) :
    R.residue₁ ⟨_, h'⟩ = R.residue₁ ⟨f, h⟩ -
      algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A a) := by
  rw [← residue₁_algebraMap R a (algebraMap_mem_integers₁ R a), ← map_sub]
  rfl

theorem residue₂_sub_algebraMap (f : ↥(modularFunctionFieldBar (N * q))) (h : f ∈ R.R₂.integers) (a : A)
    (h' : f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h'⟩ = R.residue₂ ⟨f, h⟩ -
      algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A a) := by
  rw [← residue₂_algebraMap R a (algebraMap_mem_integers₂ R a), ← map_sub]
  rfl

theorem residue₁_one_sub_smul (f : ↥(modularFunctionFieldBar (N * q))) (h : f ∈ R.R₁.integers) (a : A)
    (ha : IsLocalRing.residue A a = 0)
    (h' : 1 - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) * f ∈ R.R₁.integers) :
    R.residue₁ ⟨_, h'⟩ = 1 := by
  have hx : (⟨_, h'⟩ : R.R₁.integers) = 1 - ⟨_, algebraMap_mem_integers₁ R a⟩ * ⟨f, h⟩ := rfl
  rw [hx, map_sub, map_one, map_mul, residue₁_algebraMap R a, ha, map_zero, zero_mul, sub_zero]

theorem residue₂_one_sub_smul (f : ↥(modularFunctionFieldBar (N * q))) (h : f ∈ R.R₂.integers) (a : A)
    (ha : IsLocalRing.residue A a = 0)
    (h' : 1 - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) * f ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h'⟩ = 1 := by
  have hx : (⟨_, h'⟩ : R.R₂.integers) = 1 - ⟨_, algebraMap_mem_integers₂ R a⟩ * ⟨f, h⟩ := rfl
  rw [hx, map_sub, map_one, map_mul, residue₂_algebraMap R a, ha, map_zero, zero_mul, sub_zero]

theorem residue_ne_zero_iff₁ (x : R.R₁.integers) : R.residue₁ x ≠ 0 ↔ R.R₁.residue x ≠ 0 := by
  rw [ProlongationTuple.residue₁_apply]
  exact map_ne_zero_iff R.ι R.ι.injective

theorem residue_ne_zero_iff₂ (x : R.R₂.integers) : R.residue₂ x ≠ 0 ↔ R.R₂.residue x ≠ 0 := by
  rw [ProlongationTuple.residue₂_apply]
  exact map_ne_zero_iff R.ι R.ι.injective

end SeamN

section CoreN

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  [CharP (ResidueField A) q]
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ}
  [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))] [DecidableEq (ResidueField A)]

set_option hygiene false in
local notation "φ" => frobOnPlacesGeomLevel (ResidueField A) N data hKr
set_option hygiene false in
local notation "FNq" => ↥(modularFunctionFieldBar (N * q))
set_option hygiene false in
local notation "FN" => ↥(modularFunctionFieldC (ResidueField A) N)
set_option hygiene false in
local notation "PlFN" => Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)

set_option maxHeartbeats 6400000 in

theorem mem_of_hasValue (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (hcusp : ∀ V : Place (AlgebraicClosure ℚ) FNq, ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceFst V) → ProlongationTuple.IsCuspidal P V)
    (hsplit : ∀ V : Place (AlgebraicClosure ℚ) FNq, ProlongationTuple.IsCuspidal P V →
      ProlongationTuple.IsInftySide P V ∨ ProlongationTuple.IsZeroSide P V)
    (hInftyNA : ∀ V : Place (AlgebraicClosure ℚ) FNq, ProlongationTuple.IsInftySide P V → ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceFst V))
    (hZeroNA : ∀ V : Place (AlgebraicClosure ℚ) FNq, ProlongationTuple.IsZeroSide P V → ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceSnd V))
    (hφaff : ∀ v : PlFN, IsAffineGeomPlace (ResidueField A) N v → IsAffineGeomPlace (ResidueField A) N (φ v))
    (Z : Set PlFN)
    (hZcusp : ∀ W, ProlongationTuple.IsInftySide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z)
    (hZcusp' : ∀ W, ProlongationTuple.IsZeroSide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z) (G : FNq) (hG₁ : G ∈ R.R₁.integers) (hG₂ : G ∈ R.R₂.integers)
    (hGpole : ∀ W : Place (AlgebraicClosure ℚ) FNq, W.ord G < 0 →
      (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z))
    (V₀ : Place (AlgebraicClosure ℚ) FNq) (hd₁ : P.reduceFst V₀ ∈ Z) (hd₂ : P.reduceSnd V₀ ∈ Z)
    (c : AlgebraicClosure ℚ) (hc : V₀.HasValue G c)
    (hf0 : G - algebraMap (AlgebraicClosure ℚ) FNq c ≠ 0) : c ∈ A := by
  classical
  by_contra hcA
  have hc0 : c ≠ 0 := fun h => hcA (by rw [h]; exact A.zero_mem)
  have hcinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
  have ha0 := residue_inv_eq_zero_of_not_mem hcA hcinv
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) _ hf0
  have hDV₀ : 1 ≤ D V₀ := by
    have := ord_sub_pos_of_hasValue V₀ hc hf0
    rw [hD]; omega
  have hDpole : ∀ W, D W < 0 →
      (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z) := by
    intro W hW
    rw [hD] at hW
    exact hGpole W (ord_neg_of_ord_sub_const_neg W hW).2
  set H : FNq := 1 - algebraMap (AlgebraicClosure ℚ) FNq (((⟨c⁻¹, hcinv⟩ : A) : AlgebraicClosure ℚ)) * G
    with hH
  have hH₁ : H ∈ R.R₁.integers := sub_mem (one_mem _) (mul_mem (algebraMap_mem_integers₁ R _) hG₁)
  have hH₂ : H ∈ R.R₂.integers := sub_mem (one_mem _) (mul_mem (algebraMap_mem_integers₂ R _) hG₂)
  have hrH₁ : R.residue₁ ⟨H, hH₁⟩ = 1 := residue₁_one_sub_smul R G hG₁ ⟨c⁻¹, hcinv⟩ ha0 hH₁
  have hrH₂ : R.residue₂ ⟨H, hH₂⟩ = 1 := residue₂_one_sub_smul R G hG₂ ⟨c⁻¹, hcinv⟩ ha0 hH₂
  have hHf : H = algebraMap (AlgebraicClosure ℚ) FNq (-c⁻¹) * (G - algebraMap (AlgebraicClosure ℚ) FNq c) := by
    rw [hH, (algebraMap (AlgebraicClosure ℚ) FNq).map_neg, neg_mul, mul_sub, ← map_mul,
      inv_mul_cancel₀ hc0, map_one, neg_sub]
  have hDH : ∀ W, D W = W.ord H := fun W => by
    rw [hD, hHf, ord_const_mul W (neg_ne_zero.mpr (inv_ne_zero hc0))]
  rcases one_le_ord_residue_or R hR hO hcusp hsplit H hH₁ hH₂ (by rw [hrH₁]; exact one_ne_zero)
      (by rw [hrH₂]; exact one_ne_zero) D hDH Z hDpole hZcusp hZcusp' V₀ hDV₀ hd₁ hd₂
      (show (P.reduceFst V₀).ord (R.residue₁ ⟨H, hH₁⟩) = 0 by rw [hrH₁, Place.ord_one]).ge
      (show (P.reduceSnd V₀).ord (R.residue₂ ⟨H, hH₂⟩) = 0 by rw [hrH₂, Place.ord_one]).ge with h | h
  · rw [hrH₁, Place.ord_one] at h; exact absurd h (by norm_num)
  · rw [hrH₂, Place.ord_one] at h; exact absurd h (by norm_num)

set_option maxHeartbeats 6400000 in

theorem core_of_common_unit (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (hcusp : ∀ V : Place (AlgebraicClosure ℚ) FNq, ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceFst V) → ProlongationTuple.IsCuspidal P V)
    (hsplit : ∀ V : Place (AlgebraicClosure ℚ) FNq, ProlongationTuple.IsCuspidal P V →
      ProlongationTuple.IsInftySide P V ∨ ProlongationTuple.IsZeroSide P V)
    (hInftyNA : ∀ V : Place (AlgebraicClosure ℚ) FNq, ProlongationTuple.IsInftySide P V → ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceFst V))
    (hZeroNA : ∀ V : Place (AlgebraicClosure ℚ) FNq, ProlongationTuple.IsZeroSide P V → ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceSnd V))
    (hφaff : ∀ v : PlFN, IsAffineGeomPlace (ResidueField A) N v → IsAffineGeomPlace (ResidueField A) N (φ v))
    (T : Finset PlFN) (Z : Set PlFN)
    (hZcusp : ∀ W, ProlongationTuple.IsInftySide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z)
    (hZcusp' : ∀ W, ProlongationTuple.IsZeroSide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z)
    (hZT : ∀ v ∈ T, v ∈ Z) (hZφ' : ∀ v, φ v ∈ T → v ∈ Z)
    (hbadZ : ∀ W : Place (AlgebraicClosure ℚ) FNq,
      (P.reduceFst W ∈ T ∨ P.reduceSnd W ∈ T) → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z)
    (V₀ : Place (AlgebraicClosure ℚ) FNq) (hd₁ : P.reduceFst V₀ ∈ Z) (hd₂ : P.reduceSnd V₀ ∈ Z)
    (g₁ g₂ : FN)
    (hg₁d : (P.reduceFst V₀).ord (g₁ - algebraMap (ResidueField A) FN 0) = 1)
    (hg₂d : (P.reduceSnd V₀).ord (g₂ - algebraMap (ResidueField A) FN 1) = 1)
    (hg₁Z : ∀ z ∈ Z, z ≠ P.reduceFst V₀ →
      ∃ γ : ResidueField A, γ ∉ ({0, 1} : Finset (ResidueField A)) ∧ z.HasValue g₁ γ)
    (hg₂Z : ∀ z ∈ Z, z ≠ P.reduceSnd V₀ →
      ∃ γ : ResidueField A, γ ∉ ({0, 1} : Finset (ResidueField A)) ∧ z.HasValue g₂ γ)
    (hg₁reg : ∀ z ∈ Z, g₁ = 0 ∨ 0 ≤ z.ord g₁) (hg₂reg : ∀ z ∈ Z, g₂ = 0 ∨ 0 ≤ z.ord g₂)
    (f : FNq) (hf0 : f ≠ 0) (hf₁ : f ∈ R.R₁.integers) (hf₂ : f ∈ R.R₂.integers)
    (cbar : ResidueField A)
    (hrf₁ : R.residue₁ ⟨f, hf₁⟩ = g₁ - algebraMap (ResidueField A) FN cbar)
    (hrf₂ : R.residue₂ ⟨f, hf₂⟩ = g₂ - algebraMap (ResidueField A) FN cbar)
    (hfV₀ : 0 < V₀.ord f)
    (hfpole : ∀ W, W.ord f < 0 →
      (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z)) :
    ∃ D : Divisor (AlgebraicClosure ℚ) FNq, (∀ V, D V = V.ord f) ∧ D V₀ = 1 ∧
      (∀ V, V ≠ V₀ → 1 ≤ D V → P.reduceFst V ∈ Z → P.reduceSnd V ∈ Z → False) ∧
      ∀ V ∈ D.support, V ≠ V₀ → P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T := by
  classical
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) f hf0
  have hDV₀ : 1 ≤ D V₀ := by rw [hD]; omega
  have hDpole : ∀ W, D W < 0 →
      (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z) := by
    intro W hW
    rw [hD] at hW
    exact hfpole W hW
  have hg₁val : (P.reduceFst V₀).HasValue g₁ 0 := hasValue_of_ord_sub_pos _ (by rw [hg₁d]; norm_num)
  have hg₂val : (P.reduceSnd V₀).HasValue g₂ 1 := hasValue_of_ord_sub_pos _ (by rw [hg₂d]; norm_num)
  have hrf₁0 : g₁ - algebraMap (ResidueField A) FN cbar ≠ 0 := by
    intro h0
    have hconst : g₁ = algebraMap (ResidueField A) FN cbar := sub_eq_zero.mp h0
    rw [hconst, map_zero, sub_zero, ord_algebraMap_eq_zero] at hg₁d
    exact zero_ne_one hg₁d
  have hrf₂0 : g₂ - algebraMap (ResidueField A) FN cbar ≠ 0 := by
    intro h0
    have hconst : g₂ = algebraMap (ResidueField A) FN cbar := sub_eq_zero.mp h0
    rw [hconst, ← map_sub, ord_algebraMap_eq_zero] at hg₂d
    exact zero_ne_one hg₂d
  have hreg₁ : 0 ≤ (P.reduceFst V₀).ord (g₁ - algebraMap (ResidueField A) FN cbar) :=
    ord_sub_const_nonneg _ (hg₁reg _ hd₁) cbar
  have hreg₂ : 0 ≤ (P.reduceSnd V₀).ord (g₂ - algebraMap (ResidueField A) FN cbar) :=
    ord_sub_const_nonneg _ (hg₂reg _ hd₂) cbar

  have hcb : cbar = 0 ∨ cbar = 1 := by
    rcases one_le_ord_residue_or R hR hO hcusp hsplit f hf₁ hf₂ (by rw [hrf₁]; exact hrf₁0) (by rw [hrf₂]; exact hrf₂0)
        D hD Z hDpole hZcusp hZcusp' V₀ hDV₀ hd₁ hd₂ (by rw [hrf₁]; exact hreg₁) (by rw [hrf₂]; exact hreg₂) with h | h
    · left; rw [hrf₁] at h; exact eq_of_ord_sub_pos_of_hasValue _ hg₁val (by omega)
    · right; rw [hrf₂] at h; exact eq_of_ord_sub_pos_of_hasValue _ hg₂val (by omega)

  have hzc := eq_one_and_forall_of_orders R hR hO hcusp hsplit hInftyNA hZeroNA hφaff f hf₁ hf₂ (by rw [hrf₁]; exact hrf₁0)
    (by rw [hrf₂]; exact hrf₂0) D hD Z hDpole hZcusp hZcusp' V₀ hDV₀ hd₁ hd₂ (cbar = 0) (cbar = 1)
    (fun h => zero_ne_one (h.1.symm.trans h.2))
    (fun z hz hzd => by
      rw [hrf₁]
      obtain ⟨γ, hγ, hv⟩ := hg₁Z z hz hzd
      refine ord_sub_eq_zero_of_hasValue_ne z hv ?_
      rintro rfl
      rcases hcb with h | h <;> simp [h] at hγ)
    (fun z hz hzd => by
      rw [hrf₂]
      obtain ⟨γ, hγ, hv⟩ := hg₂Z z hz hzd
      refine ord_sub_eq_zero_of_hasValue_ne z hv ?_
      rintro rfl
      rcases hcb with h | h <;> simp [h] at hγ)
    (fun h => by rw [hrf₁, h]; exact hg₁d)
    (fun h => by rw [hrf₁]; exact ord_sub_eq_zero_of_hasValue_ne _ hg₁val (Ne.symm h))
    (fun h => by rw [hrf₂, h]; exact hg₂d)
    (fun h => by rw [hrf₂]; exact ord_sub_eq_zero_of_hasValue_ne _ hg₂val (Ne.symm h))
  obtain ⟨hDV₀1, hothers⟩ := hzc
  refine ⟨D, hD, hDV₀1, hothers, ?_⟩
  intro V hV hVne
  have hDV : D V ≠ 0 := Finsupp.mem_support_iff.mp hV
  rcases lt_or_gt_of_ne hDV with hneg | hpos
  ·
    rcases hDpole V hneg with ⟨h1, hZ1⟩ | ⟨h2, hZ2⟩
    · refine ⟨fun hT' => hZ1 (hZT _ hT'), fun hT' => hZ1 (hZφ' _ ?_)⟩
      rw [h1.1]; exact hT'
    · refine ⟨fun hT' => hZ2 (hZφ' _ ?_), fun hT' => hZ2 (hZT _ hT')⟩
      rw [← h2.1]; exact hT'
  ·
    by_contra hbad
    have hbad' : P.reduceFst V ∈ T ∨ P.reduceSnd V ∈ T := by
      by_contra h'
      push Not at h'
      exact hbad h'
    obtain ⟨hz1, hz2⟩ := hbadZ V hbad'
    exact hothers V hVne (by omega) hz1 hz2

end CoreN

section AssemblyN

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  [CharP (ResidueField A) q] [IsAlgClosed (ResidueField A)] [DecidableEq (ResidueField A)]
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ}
  [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))]
  [IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))]
  [IsCurveOver (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)]

set_option hygiene false in
local notation "κ" => ResidueField A
set_option hygiene false in
local notation "φ" => frobOnPlacesGeomLevel (ResidueField A) N data hKr
set_option hygiene false in
local notation "FNq" => ↥(modularFunctionFieldBar (N * q))
set_option hygiene false in
local notation "FN" => ↥(modularFunctionFieldC (ResidueField A) N)
set_option hygiene false in
local notation "PlFN" => Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)

theorem finsuppDegree_sum_single {α ι : Type*} [DecidableEq α] [Fintype ι] (Q : ι → α) :
    Finsupp.degree (∑ i, Finsupp.single (Q i) (1 : ℤ)) = Fintype.card ι := by
  classical
  rw [map_sum]
  simp [Finsupp.degree_single]

theorem one_le_sum_single_apply_self {α ι : Type*} [Fintype ι] (Q : ι → α) (i : ι) :
    1 ≤ (∑ j, Finsupp.single (Q j) (1 : ℤ)) (Q i) := by
  classical
  rw [sum_single_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num)

theorem mapDomain_sum_single {α β : Type*} {ι : Type*} [Fintype ι] (r : α → β) (Q : ι → α) :
    Finsupp.mapDomain r (∑ i, Finsupp.single (Q i) (1 : ℤ)) = ∑ i, Finsupp.single (r (Q i)) (1 : ℤ) := by
  classical
  rw [Finsupp.mapDomain_finset_sum]
  exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_single

set_option maxHeartbeats 12800000 in

theorem coreN (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset PlFN) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N κ)
    (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hqN : ¬ q ∣ N)

    (hcusp : ∀ V : Place (AlgebraicClosure ℚ) FNq, ¬ IsAffineGeomPlace κ N (P.reduceFst V) → ProlongationTuple.IsCuspidal P V)
    (hsplit : ∀ V : Place (AlgebraicClosure ℚ) FNq, ProlongationTuple.IsCuspidal P V →
      ProlongationTuple.IsInftySide P V ∨ ProlongationTuple.IsZeroSide P V)
    (hInftyNA : ∀ V : Place (AlgebraicClosure ℚ) FNq, ProlongationTuple.IsInftySide P V → ¬ IsAffineGeomPlace κ N (P.reduceFst V))
    (hInftyNA' : ∀ V : Place (AlgebraicClosure ℚ) FNq, ProlongationTuple.IsInftySide P V → ¬ IsAffineGeomPlace κ N (P.reduceSnd V))
    (hZeroNA : ∀ V : Place (AlgebraicClosure ℚ) FNq, ProlongationTuple.IsZeroSide P V → ¬ IsAffineGeomPlace κ N (P.reduceSnd V))
    (hZeroNA' : ∀ V : Place (AlgebraicClosure ℚ) FNq, ProlongationTuple.IsZeroSide P V → ¬ IsAffineGeomPlace κ N (P.reduceFst V))
    (hφaff : ∀ v : PlFN, IsAffineGeomPlace κ N v → IsAffineGeomPlace κ N (φ v))

    (hNss : ∀ s ∈ nodePairsOfPlaces (arithFrobC q κ N) W, s.1 ∈ ssPlaces q N κ ∧ s.2 ∈ ssPlaces q N κ)

    (hzone : ∀ T : Finset PlFN, (∀ t ∈ T, t ∉ ssPlaces q N κ) →
      ∃ Z : Finset PlFN, (∀ v ∈ T, v ∈ Z) ∧ (∀ v ∈ T, φ v ∈ Z) ∧ (∀ v, φ v ∈ T → v ∈ Z) ∧
        (∀ v, ¬ IsAffineGeomPlace κ N v → v ∈ Z) ∧ (∀ v, φ (φ v) = v → v ∉ ssPlaces q N κ → v ∈ Z) ∧
        (∀ v ∈ Z, v ∉ ssPlaces q N κ))

    (hAUX : ∀ (B : Finset PlFN) (m₁ m₂ : ℕ),
      ∃ (Q₁ : Fin m₁ → Place (AlgebraicClosure ℚ) FNq) (Q₂ : Fin m₂ → Place (AlgebraicClosure ℚ) FNq),
        (∀ i, P.IsStrictFst (Q₁ i)) ∧ (∀ j, P.IsStrictSnd (Q₂ j)) ∧
        (Function.Injective fun i => P.reduceFst (Q₁ i)) ∧ (Function.Injective fun j => P.reduceSnd (Q₂ j)) ∧
        (∀ i, P.reduceFst (Q₁ i) ∉ B) ∧ (∀ j, P.reduceSnd (Q₂ j) ∉ B))

    (hINTERP : ∀ (U Zv Za : Finset PlFN) (t₀ : PlFN) (β : κ) (val : PlFN → κ) (bad : Finset κ),
      Disjoint U Zv → Disjoint U Za → Disjoint Zv Za → t₀ ∉ U → t₀ ∉ Zv → t₀ ∉ Za →
      Zv.card + 2 * genusFF κ FN + 2 ≤ U.card →
      ∃ g : FN, g ∈ riemannRochSpace (∑ u ∈ U, Finsupp.single u (1 : ℤ)) ∧
        t₀.ord (g - algebraMap κ FN β) = 1 ∧ (∀ z ∈ Zv, z.HasValue g (val z)) ∧
        (∀ z ∈ Za, ∃ γ : κ, γ ∉ bad ∧ z.HasValue g γ))

    (hREALN : ∀ (D : Divisor (AlgebraicClosure ℚ) FNq), 0 ≤ D → P.IsGoodDiv D →
      2 * (genusFF κ FN : ℤ) - 1 + W.card ≤ (Finsupp.mapDomain P.reduceFst (P.fstDiv D)).degree →
      2 * (genusFF κ FN : ℤ) - 1 ≤ (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)).degree →
      ∀ (g₁ g₂ : ↥(modularFunctionFieldFullC κ N)),
        (R.ι g₁ : FN) ∈ riemannRochSpace (Finsupp.mapDomain P.reduceFst (P.fstDiv D)) →
        (R.ι g₂ : FN) ∈ riemannRochSpace (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)) →
        (∀ s ∈ nodePairsOfPlaces (arithFrobC q κ N) W, ∃ c : κ,
          s.1.HasValue (R.ι g₁ : FN) c ∧ s.2.HasValue (R.ι g₂ : FN) c) →
        ∃ (G : FNq) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers),
          G ∈ riemannRochSpace D ∧ R.R₁.residue ⟨G, h₁⟩ = g₁ ∧ R.R₂.residue ⟨G, h₂⟩ = g₂)

    (toFull : FN → ↥(modularFunctionFieldFullC κ N)) (ι_toFull : ∀ g : FN, R.ι (toFull g) = g)

    (T : Finset PlFN) (hT : ∀ t ∈ T, t ∉ ssPlaces q N κ)
    (V₀ : Place (AlgebraicClosure ℚ) FNq) (hV₀ : P.reduceFst V₀ ∈ T ∨ P.reduceSnd V₀ ∈ T) :
    ∃ (Z : Finset PlFN) (f : FNq) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
      (D : Divisor (AlgebraicClosure ℚ) FNq),

      ((∀ v ∈ T, v ∈ Z) ∧ (∀ v, ¬ IsAffineGeomPlace κ N v → v ∈ Z) ∧
        (∀ v, φ (φ v) = v → v ∉ ssPlaces q N κ → v ∈ Z) ∧ (∀ v ∈ Z, v ∉ ssPlaces q N κ)) ∧
      f ≠ 0 ∧ R.residue₁ ⟨f, h₁⟩ ≠ 0 ∧ R.residue₂ ⟨f, h₂⟩ ≠ 0 ∧
      (∀ V, D V = V.ord f) ∧ D V₀ = 1 ∧
      (∀ V, D V < 0 → (P.IsStrictFst V ∧ P.reduceFst V ∉ Z) ∨ (P.IsStrictSnd V ∧ P.reduceSnd V ∉ Z)) ∧

      (∀ z, (z ∈ Z ∨ z ∈ W) → z ≠ P.reduceFst V₀ → z.ord (R.residue₁ ⟨f, h₁⟩) = 0) ∧
      (∀ z, (z ∈ Z ∨ z ∈ W) → z ≠ P.reduceSnd V₀ → z.ord (R.residue₂ ⟨f, h₂⟩) = 0) ∧
      (((P.reduceFst V₀).ord (R.residue₁ ⟨f, h₁⟩) = 1 ∧ (P.reduceSnd V₀).ord (R.residue₂ ⟨f, h₂⟩) = 0) ∨
        ((P.reduceFst V₀).ord (R.residue₁ ⟨f, h₁⟩) = 0 ∧ (P.reduceSnd V₀).ord (R.residue₂ ⟨f, h₂⟩) = 1)) ∧
      (∀ V, V ≠ V₀ → 1 ≤ D V → P.reduceFst V ∈ Z → P.reduceSnd V ∈ Z → False) ∧
      ∀ V ∈ D.support, V ≠ V₀ → P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T := by
  classical
  haveI : Infinite κ := inferInstance
  have hφinj := ModularCurve.frobOnPlacesGeomLevel_injective κ N data hKr

  obtain ⟨Z, hZT, hZφ, hZφ', hZna, hZfix, hZss⟩ := hzone T hT
  have hbadZ : ∀ V : Place (AlgebraicClosure ℚ) FNq, (P.reduceFst V ∈ T ∨ P.reduceSnd V ∈ T) →
      P.reduceFst V ∈ Z ∧ P.reduceSnd V ∈ Z := by
    intro V hV
    rcases P.d1 V with h | h
    · change P.reduceFst V = φ (P.reduceSnd V) at h
      rcases hV with hV | hV
      · exact ⟨hZT _ hV, hZφ' _ (by rw [← h]; exact hV)⟩
      · exact ⟨by rw [h]; exact hZφ _ hV, hZT _ hV⟩
    · change φ (P.reduceFst V) = P.reduceSnd V at h
      rcases hV with hV | hV
      · exact ⟨hZT _ hV, by rw [← h]; exact hZφ _ hV⟩
      · exact ⟨hZφ' _ (by rw [h]; exact hV), hZT _ hV⟩
  have hZcusp : ∀ V, ProlongationTuple.IsInftySide P V → P.reduceFst V ∈ (↑Z : Set PlFN) ∧ P.reduceSnd V ∈ (↑Z : Set PlFN) :=
    fun V hV => ⟨Finset.mem_coe.mpr (hZna _ (hInftyNA V hV)), Finset.mem_coe.mpr (hZna _ (hInftyNA' V hV))⟩
  have hZcusp' : ∀ V, ProlongationTuple.IsZeroSide P V → P.reduceFst V ∈ (↑Z : Set PlFN) ∧ P.reduceSnd V ∈ (↑Z : Set PlFN) :=
    fun V hV => ⟨Finset.mem_coe.mpr (hZna _ (hZeroNA' V hV)), Finset.mem_coe.mpr (hZna _ (hZeroNA V hV))⟩
  obtain ⟨hd₁, hd₂⟩ := hbadZ V₀ hV₀
  have hWss : ∀ v ∈ W, v ∈ ssPlaces q N κ := fun v hv => (hW v).mp hv

  set Np := nodePairsOfPlaces (arithFrobC q κ N) W with hNp

  set m : ℕ := 2 * genusFF κ FN + W.card + Np.card + 2 with hm
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hinj₁, hinj₂, hB₁, hB₂⟩ := hAUX (Z ∪ W) m m
  have hB₁Z : ∀ i, P.reduceFst (Q₁ i) ∉ Z := fun i h => hB₁ i (Finset.mem_union_left _ h)
  have hB₂Z : ∀ j, P.reduceSnd (Q₂ j) ∉ Z := fun j h => hB₂ j (Finset.mem_union_left _ h)
  have hB₁N : ∀ i, P.reduceFst (Q₁ i) ∉ W := fun i h => hB₁ i (Finset.mem_union_right _ h)
  have hB₂N : ∀ j, P.reduceSnd (Q₂ j) ∉ W := fun j h => hB₂ j (Finset.mem_union_right _ h)
  set E₁ : Divisor (AlgebraicClosure ℚ) FNq := ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) with hE₁
  set E₂ : Divisor (AlgebraicClosure ℚ) FNq := ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) with hE₂
  set Daux : Divisor (AlgebraicClosure ℚ) FNq := E₁ + E₂ with hDaux
  have hDaux0 : ∀ V, 0 ≤ Daux V := fun V => by
    rw [hDaux, Finsupp.add_apply]
    exact add_nonneg (sum_single_apply_nonneg Q₁ V) (sum_single_apply_nonneg Q₂ V)
  have hDaux_cases : ∀ V, Daux V ≠ 0 → (∃ i, Q₁ i = V) ∨ (∃ j, Q₂ j = V) := by
    intro V hV
    by_contra hc
    push Not at hc
    apply hV
    rw [hDaux, Finsupp.add_apply, sum_single_apply_eq_zero Q₁ V hc.1, sum_single_apply_eq_zero Q₂ V hc.2, add_zero]
  have hgood : P.IsGoodDiv Daux := by
    intro V hV
    rcases hDaux_cases V (Finsupp.mem_support_iff.mp hV) with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl (hQ₁ i)
    · exact Or.inr (hQ₂ j)
  have hDQ₁ : ∀ i, 1 ≤ Daux (Q₁ i) := fun i => by
    rw [hDaux, Finsupp.add_apply]
    exact le_add_of_le_of_nonneg (one_le_sum_single_apply_self Q₁ i) (sum_single_apply_nonneg Q₂ _)
  have hDQ₂ : ∀ j, 1 ≤ Daux (Q₂ j) := fun j => by
    rw [hDaux, Finsupp.add_apply]
    exact le_add_of_nonneg_of_le (sum_single_apply_nonneg Q₁ _) (one_le_sum_single_apply_self Q₂ j)

  have hfst : P.fstDiv Daux = E₁ := by
    unfold PlaceSpecialization.fstDiv
    rw [hDaux, Finsupp.filter_add]
    have h1 : E₁.filter P.IsStrictFst = E₁ := by
      rw [Finsupp.filter_eq_self_iff]
      intro V hV
      obtain ⟨i, rfl⟩ := exists_of_sum_single_apply_ne_zero Q₁ V hV
      exact hQ₁ i
    have h2 : E₂.filter P.IsStrictFst = 0 := by
      rw [Finsupp.filter_eq_zero_iff]
      intro V hV
      by_contra h0
      obtain ⟨j, rfl⟩ := exists_of_sum_single_apply_ne_zero Q₂ V h0
      exact not_isStrictSnd_of_isStrictFst hV (hQ₂ j)
    rw [h1, h2, add_zero]
  have hsnd : P.sndDiv Daux = E₂ := by
    unfold PlaceSpecialization.sndDiv
    rw [hDaux, Finsupp.filter_add]
    have h1 : E₁.filter P.IsStrictSnd = 0 := by
      rw [Finsupp.filter_eq_zero_iff]
      intro V hV
      by_contra h0
      obtain ⟨i, rfl⟩ := exists_of_sum_single_apply_ne_zero Q₁ V h0
      exact not_isStrictSnd_of_isStrictFst (hQ₁ i) hV
    have h2 : E₂.filter P.IsStrictSnd = E₂ := by
      rw [Finsupp.filter_eq_self_iff]
      intro V hV
      obtain ⟨j, rfl⟩ := exists_of_sum_single_apply_ne_zero Q₂ V hV
      exact hQ₂ j
    rw [h1, h2, zero_add]

  set U₁ : Finset PlFN := Finset.univ.image (fun i => P.reduceFst (Q₁ i)) with hU₁
  set U₂ : Finset PlFN := Finset.univ.image (fun j => P.reduceSnd (Q₂ j)) with hU₂
  have hU₁card : U₁.card = m := by
    rw [hU₁, Finset.card_image_of_injective _ hinj₁, Finset.card_univ, Fintype.card_fin]
  have hU₂card : U₂.card = m := by
    rw [hU₂, Finset.card_image_of_injective _ hinj₂, Finset.card_univ, Fintype.card_fin]
  have hmemU₁ : ∀ {v}, v ∈ U₁ → ∃ i, P.reduceFst (Q₁ i) = v := fun {v} hv => by simpa [hU₁] using hv
  have hmemU₂ : ∀ {v}, v ∈ U₂ → ∃ j, P.reduceSnd (Q₂ j) = v := fun {v} hv => by simpa [hU₂] using hv
  have hU₁Z : ∀ v ∈ U₁, v ∉ Z := by intro v hv; obtain ⟨i, rfl⟩ := hmemU₁ hv; exact hB₁Z i
  have hU₂Z : ∀ v ∈ U₂, v ∉ Z := by intro v hv; obtain ⟨j, rfl⟩ := hmemU₂ hv; exact hB₂Z j
  have hsumU : ∀ (U : Finset PlFN) (v : PlFN), (∑ u ∈ U, Finsupp.single u (1 : ℤ)) v = if v ∈ U then 1 else 0 := by
    intro U v
    rw [Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply, Finset.sum_ite_eq']
  have hmapE₁ : Finsupp.mapDomain P.reduceFst E₁ = ∑ i, Finsupp.single (P.reduceFst (Q₁ i)) (1 : ℤ) :=
    mapDomain_sum_single _ _
  have hmapE₂ : Finsupp.mapDomain P.reduceSnd E₂ = ∑ j, Finsupp.single (P.reduceSnd (Q₂ j)) (1 : ℤ) :=
    mapDomain_sum_single _ _
  have hL₁ : riemannRochSpace (∑ u ∈ U₁, Finsupp.single u (1 : ℤ)) ≤
      riemannRochSpace (Finsupp.mapDomain P.reduceFst (P.fstDiv Daux)) := by
    refine riemannRochSpace_mono fun v => ?_
    rw [hsumU, hfst, hmapE₁]
    split_ifs with hv
    · obtain ⟨i, rfl⟩ := hmemU₁ hv
      exact one_le_sum_single_apply_self (fun i => P.reduceFst (Q₁ i)) i
    · exact sum_single_apply_nonneg _ _
  have hL₂ : riemannRochSpace (∑ u ∈ U₂, Finsupp.single u (1 : ℤ)) ≤
      riemannRochSpace (Finsupp.mapDomain P.reduceSnd (P.sndDiv Daux)) := by
    refine riemannRochSpace_mono fun v => ?_
    rw [hsumU, hsnd, hmapE₂]
    split_ifs with hv
    · obtain ⟨j, rfl⟩ := hmemU₂ hv
      exact one_le_sum_single_apply_self (fun j => P.reduceSnd (Q₂ j)) j
    · exact sum_single_apply_nonneg _ _
  have hdeg₁ : 2 * (genusFF κ FN : ℤ) - 1 + W.card ≤ (Finsupp.mapDomain P.reduceFst (P.fstDiv Daux)).degree := by
    rw [hfst, hmapE₁, finsuppDegree_sum_single, Fintype.card_fin, hm]; push_cast; omega
  have hdeg₂ : 2 * (genusFF κ FN : ℤ) - 1 ≤ (Finsupp.mapDomain P.reduceSnd (P.sndDiv Daux)).degree := by
    rw [hsnd, hmapE₂, finsuppDegree_sum_single, Fintype.card_fin, hm]; push_cast; omega

  obtain ⟨γ₀, hγ₀⟩ := Infinite.exists_notMem_finset ({(0 : κ), 1} : Finset κ)
  have hU₁N₁ : Disjoint U₁ W := Finset.disjoint_left.mpr fun v hvU hvN => by
    obtain ⟨i, rfl⟩ := hmemU₁ hvU; exact hB₁N i hvN
  have hU₂N₂ : Disjoint U₂ W := Finset.disjoint_left.mpr fun v hvU hvN => by
    obtain ⟨j, rfl⟩ := hmemU₂ hvU; exact hB₂N j hvN
  have hU₁Za : Disjoint U₁ (Z.erase (P.reduceFst V₀)) := Finset.disjoint_left.mpr fun v hvU hvZ =>
    hU₁Z v hvU (Finset.mem_of_mem_erase hvZ)
  have hU₂Za : Disjoint U₂ (Z.erase (P.reduceSnd V₀)) := Finset.disjoint_left.mpr fun v hvU hvZ =>
    hU₂Z v hvU (Finset.mem_of_mem_erase hvZ)
  have hN₁Za : Disjoint W (Z.erase (P.reduceFst V₀)) := Finset.disjoint_left.mpr fun v hvN hvZ =>
    hZss v (Finset.mem_of_mem_erase hvZ) (hWss v hvN)
  have hN₂Za : Disjoint W (Z.erase (P.reduceSnd V₀)) := Finset.disjoint_left.mpr fun v hvN hvZ =>
    hZss v (Finset.mem_of_mem_erase hvZ) (hWss v hvN)
  have hd₁U : P.reduceFst V₀ ∉ U₁ := fun h => hU₁Z _ h hd₁
  have hd₂U : P.reduceSnd V₀ ∉ U₂ := fun h => hU₂Z _ h hd₂
  have hd₁N : P.reduceFst V₀ ∉ W := fun h => hZss _ hd₁ (hWss _ h)
  have hd₂N : P.reduceSnd V₀ ∉ W := fun h => hZss _ hd₂ (hWss _ h)
  have hd₁Za : P.reduceFst V₀ ∉ Z.erase (P.reduceFst V₀) := Finset.notMem_erase _ _
  have hd₂Za : P.reduceSnd V₀ ∉ Z.erase (P.reduceSnd V₀) := Finset.notMem_erase _ _
  have hcard₁ : W.card + 2 * genusFF κ FN + 2 ≤ U₁.card := by rw [hU₁card, hm]; omega
  have hcard₂ : W.card + 2 * genusFF κ FN + 2 ≤ U₂.card := by rw [hU₂card, hm]; omega
  obtain ⟨g₁, hg₁L, hg₁d, hg₁N, hg₁Z⟩ := hINTERP U₁ W (Z.erase (P.reduceFst V₀)) (P.reduceFst V₀) 0 (fun _ => γ₀) {0, 1}
    hU₁N₁ hU₁Za hN₁Za hd₁U hd₁N hd₁Za hcard₁
  obtain ⟨g₂, hg₂L, hg₂d, hg₂N, hg₂Z⟩ := hINTERP U₂ W (Z.erase (P.reduceSnd V₀)) (P.reduceSnd V₀) 1 (fun _ => γ₀) {0, 1}
    hU₂N₂ hU₂Za hN₂Za hd₂U hd₂N hd₂Za hcard₂
  have hg₁val : (P.reduceFst V₀).HasValue g₁ 0 := hasValue_of_ord_sub_pos _ (by rw [hg₁d]; norm_num)
  have hg₂val : (P.reduceSnd V₀).HasValue g₂ 1 := hasValue_of_ord_sub_pos _ (by rw [hg₂d]; norm_num)
  have hg₁reg : ∀ z ∈ (↑Z : Set PlFN), g₁ = 0 ∨ 0 ≤ z.ord g₁ := fun z hz =>
    ord_nonneg_of_mem_riemannRochSpace hg₁L z (by rw [hsumU, if_neg (fun h => hU₁Z z h (Finset.mem_coe.mp hz))])
  have hg₂reg : ∀ z ∈ (↑Z : Set PlFN), g₂ = 0 ∨ 0 ≤ z.ord g₂ := fun z hz =>
    ord_nonneg_of_mem_riemannRochSpace hg₂L z (by rw [hsumU, if_neg (fun h => hU₂Z z h (Finset.mem_coe.mp hz))])

  have hg₁F : (R.ι (toFull g₁) : FN) ∈ riemannRochSpace (Finsupp.mapDomain P.reduceFst (P.fstDiv Daux)) := by
    rw [ι_toFull]; exact hL₁ hg₁L
  have hg₂F : (R.ι (toFull g₂) : FN) ∈ riemannRochSpace (Finsupp.mapDomain P.reduceSnd (P.sndDiv Daux)) := by
    rw [ι_toFull]; exact hL₂ hg₂L
  have hnode : ∀ s ∈ nodePairsOfPlaces (arithFrobC q κ N) W, ∃ c : κ,
      s.1.HasValue (R.ι (toFull g₁) : FN) c ∧ s.2.HasValue (R.ι (toFull g₂) : FN) c := by
    intro s hs
    refine ⟨γ₀, ?_, ?_⟩
    · rw [ι_toFull]; exact hg₁N _ ((hW _).mpr (hNss s hs).1)
    · rw [ι_toFull]; exact hg₂N _ ((hW _).mpr (hNss s hs).2)
  obtain ⟨G, hG₁, hG₂, hGL, hr₁, hr₂⟩ :=
    hREALN Daux (fun V => hDaux0 V) hgood hdeg₁ hdeg₂ (toFull g₁) (toFull g₂) hg₁F hg₂F hnode
  have hres₁ : R.residue₁ ⟨G, hG₁⟩ = g₁ := by rw [ProlongationTuple.residue₁_apply, hr₁, ι_toFull]
  have hres₂ : R.residue₂ ⟨G, hG₂⟩ = g₂ := by rw [ProlongationTuple.residue₂_apply, hr₂, ι_toFull]
  have hg₁ne : g₁ ≠ 0 := by
    intro h; rw [h, map_zero, sub_zero, Place.ord_zero] at hg₁d; exact zero_ne_one hg₁d
  have hG0 : G ≠ 0 := by
    intro h0
    apply hg₁ne
    rw [← hres₁]
    have : (⟨G, hG₁⟩ : R.R₁.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hGpole : ∀ V, V.ord G < 0 → (∃ i, Q₁ i = V) ∨ (∃ j, Q₂ j = V) := by
    intro V hV
    apply hDaux_cases
    rcases (mem_riemannRochSpace_iff.mp hGL) V with h | h
    · exact absurd h hG0
    · omega

  have hV₀notQ : Daux V₀ = 0 := by
    by_contra h
    rcases hDaux_cases V₀ h with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact hB₁Z i (by rw [hi]; exact hd₁)
    · exact hB₂Z j (by rw [hj]; exact hd₂)
  obtain ⟨c, hc⟩ := exists_hasValue_of_ord_nonneg V₀ (ord_nonneg_of_mem_riemannRochSpace hGL V₀ hV₀notQ)
  set f : FNq := G - algebraMap (AlgebraicClosure ℚ) FNq c with hf
  have hf0 : f ≠ 0 := by
    intro h0
    have hGc : G = algebraMap (AlgebraicClosure ℚ) FNq c := sub_eq_zero.mp h0
    have hcA : c ∈ A := (R.R₁.algebraMap_mem_iff c).mp (by rw [← hGc]; exact hG₁)
    have hconst : g₁ = algebraMap κ FN (IsLocalRing.residue A ⟨c, hcA⟩) := by
      rw [← hres₁]
      have hx : (⟨G, hG₁⟩ : R.R₁.integers) =
          ⟨algebraMap (AlgebraicClosure ℚ) FNq (((⟨c, hcA⟩ : A) : AlgebraicClosure ℚ)), algebraMap_mem_integers₁ R ⟨c, hcA⟩⟩ :=
        Subtype.ext hGc
      rw [hx, residue₁_algebraMap]
    rw [hconst, map_zero, sub_zero, ord_algebraMap_eq_zero] at hg₁d
    exact zero_ne_one hg₁d
  have hGpoleZ : ∀ V : Place (AlgebraicClosure ℚ) FNq, V.ord G < 0 →
      (P.IsStrictFst V ∧ P.reduceFst V ∉ (↑Z : Set PlFN)) ∨ (P.IsStrictSnd V ∧ P.reduceSnd V ∉ (↑Z : Set PlFN)) := by
    intro V hV
    rcases hGpole V hV with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl ⟨hQ₁ i, fun h => hB₁Z i (Finset.mem_coe.mp h)⟩
    · exact Or.inr ⟨hQ₂ j, fun h => hB₂Z j (Finset.mem_coe.mp h)⟩
  have hcA : c ∈ A := mem_of_hasValue R hR hO hcusp hsplit hInftyNA hZeroNA hφaff (↑Z) hZcusp hZcusp' G hG₁ hG₂ hGpoleZ
    V₀ (Finset.mem_coe.mpr hd₁) (Finset.mem_coe.mpr hd₂) c hc hf0

  have hf₁ : f ∈ R.R₁.integers := sub_mem hG₁ (algebraMap_mem_integers₁ R ⟨c, hcA⟩)
  have hf₂ : f ∈ R.R₂.integers := sub_mem hG₂ (algebraMap_mem_integers₂ R ⟨c, hcA⟩)
  set cbar : κ := IsLocalRing.residue A ⟨c, hcA⟩ with hcbar
  have hrf₁ : R.residue₁ ⟨f, hf₁⟩ = g₁ - algebraMap κ FN cbar := by
    rw [← hres₁]; exact residue₁_sub_algebraMap R G hG₁ ⟨c, hcA⟩ hf₁
  have hrf₂ : R.residue₂ ⟨f, hf₂⟩ = g₂ - algebraMap κ FN cbar := by
    rw [← hres₂]; exact residue₂_sub_algebraMap R G hG₂ ⟨c, hcA⟩ hf₂
  have hfV₀ : 0 < V₀.ord f := ord_sub_pos_of_hasValue V₀ hc hf0
  have hfpole : ∀ V, V.ord f < 0 →
      (P.IsStrictFst V ∧ P.reduceFst V ∉ (↑Z : Set PlFN)) ∨ (P.IsStrictSnd V ∧ P.reduceSnd V ∉ (↑Z : Set PlFN)) :=
    fun V hV => hGpoleZ V (ord_neg_of_ord_sub_const_neg V hV).2
  obtain ⟨D, hD, hDV₀1, hcount, hgoodT⟩ := core_of_common_unit R hR hO hcusp hsplit hInftyNA hZeroNA hφaff T (↑Z) hZcusp hZcusp'
    (fun v hv => Finset.mem_coe.mpr (hZT v hv)) (fun v hv => Finset.mem_coe.mpr (hZφ' v hv))
    (fun V hV => ⟨Finset.mem_coe.mpr (hbadZ V hV).1, Finset.mem_coe.mpr (hbadZ V hV).2⟩) V₀
    (Finset.mem_coe.mpr hd₁) (Finset.mem_coe.mpr hd₂)
    g₁ g₂ hg₁d hg₂d (fun z hz hne => hg₁Z z (Finset.mem_erase.mpr ⟨hne, Finset.mem_coe.mp hz⟩))
    (fun z hz hne => hg₂Z z (Finset.mem_erase.mpr ⟨hne, Finset.mem_coe.mp hz⟩)) hg₁reg hg₂reg f hf0 hf₁ hf₂ cbar hrf₁ hrf₂ hfV₀ hfpole

  have hrf₁0 : R.residue₁ ⟨f, hf₁⟩ ≠ 0 := by
    rw [hrf₁]; intro h0
    have hconst : g₁ = algebraMap κ FN cbar := sub_eq_zero.mp h0
    rw [hconst, map_zero, sub_zero, ord_algebraMap_eq_zero] at hg₁d
    exact zero_ne_one hg₁d
  have hrf₂0 : R.residue₂ ⟨f, hf₂⟩ ≠ 0 := by
    rw [hrf₂]; intro h0
    have hconst : g₂ = algebraMap κ FN cbar := sub_eq_zero.mp h0
    rw [hconst, ← map_sub, ord_algebraMap_eq_zero] at hg₂d
    exact zero_ne_one hg₂d
  have hDpole' : ∀ V, D V < 0 → P.IsStrictFst V ∨ P.IsStrictSnd V := by
    intro V hV
    rw [hD] at hV
    rcases hfpole V hV with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h

  have hcb01 : cbar = 0 ∨ cbar = 1 := by

    have hreg₁ : 0 ≤ (P.reduceFst V₀).ord (g₁ - algebraMap κ FN cbar) := ord_sub_const_nonneg _ (hg₁reg _ (Finset.mem_coe.mpr hd₁)) cbar
    have hreg₂ : 0 ≤ (P.reduceSnd V₀).ord (g₂ - algebraMap κ FN cbar) := ord_sub_const_nonneg _ (hg₂reg _ (Finset.mem_coe.mpr hd₂)) cbar
    have hDV₀ : 1 ≤ D V₀ := by rw [hDV₀1]
    rcases one_le_ord_residue_or R hR hO hcusp hsplit f hf₁ hf₂ hrf₁0 hrf₂0 D hD (↑Z)
        (fun V hV => by rw [hD] at hV; exact hfpole V hV) hZcusp hZcusp' V₀ hDV₀
        (Finset.mem_coe.mpr hd₁) (Finset.mem_coe.mpr hd₂) (by rw [hrf₁]; exact hreg₁) (by rw [hrf₂]; exact hreg₂) with h | h
    · left; rw [hrf₁] at h; exact eq_of_ord_sub_pos_of_hasValue _ hg₁val (by omega)
    · right; rw [hrf₂] at h; exact eq_of_ord_sub_pos_of_hasValue _ hg₂val (by omega)
  have hγc : γ₀ - cbar ≠ 0 := by
    intro h0
    have : γ₀ = cbar := sub_eq_zero.mp h0
    rcases hcb01 with h | h <;> simp [this, h] at hγ₀

  have htab₁ : ∀ z, (z ∈ Z ∨ z ∈ W) → z ≠ P.reduceFst V₀ → z.ord (R.residue₁ ⟨f, hf₁⟩) = 0 := by
    intro z hz hne
    rw [hrf₁]
    rcases hz with hz | hz
    · obtain ⟨γ, hγ, hv⟩ := hg₁Z z (Finset.mem_erase.mpr ⟨hne, hz⟩)
      refine ord_sub_eq_zero_of_hasValue_ne z hv ?_
      rintro rfl
      rcases hcb01 with h | h <;> simp [h] at hγ
    · exact ord_sub_eq_zero_of_hasValue_ne z (hg₁N z hz) (fun h => hγc (sub_eq_zero.mpr h))
  have htab₂ : ∀ z, (z ∈ Z ∨ z ∈ W) → z ≠ P.reduceSnd V₀ → z.ord (R.residue₂ ⟨f, hf₂⟩) = 0 := by
    intro z hz hne
    rw [hrf₂]
    rcases hz with hz | hz
    · obtain ⟨γ, hγ, hv⟩ := hg₂Z z (Finset.mem_erase.mpr ⟨hne, hz⟩)
      refine ord_sub_eq_zero_of_hasValue_ne z hv ?_
      rintro rfl
      rcases hcb01 with h | h <;> simp [h] at hγ
    · exact ord_sub_eq_zero_of_hasValue_ne z (hg₂N z hz) (fun h => hγc (sub_eq_zero.mpr h))
  have hpat : ((P.reduceFst V₀).ord (R.residue₁ ⟨f, hf₁⟩) = 1 ∧ (P.reduceSnd V₀).ord (R.residue₂ ⟨f, hf₂⟩) = 0) ∨
      ((P.reduceFst V₀).ord (R.residue₁ ⟨f, hf₁⟩) = 0 ∧ (P.reduceSnd V₀).ord (R.residue₂ ⟨f, hf₂⟩) = 1) := by
    rcases hcb01 with h | h
    · left
      refine ⟨by rw [hrf₁, h]; exact hg₁d, ?_⟩
      rw [hrf₂]; exact ord_sub_eq_zero_of_hasValue_ne _ hg₂val (by rw [h]; exact one_ne_zero)
    · right
      refine ⟨?_, by rw [hrf₂, h]; exact hg₂d⟩
      rw [hrf₁]; exact ord_sub_eq_zero_of_hasValue_ne _ hg₁val (by rw [h]; exact zero_ne_one)
  have hDpoleZ : ∀ V, D V < 0 → (P.IsStrictFst V ∧ P.reduceFst V ∉ Z) ∨ (P.IsStrictSnd V ∧ P.reduceSnd V ∉ Z) := by
    intro V hV
    rw [hD] at hV
    rcases hfpole V hV with ⟨h, hZ'⟩ | ⟨h, hZ'⟩
    · exact Or.inl ⟨h, fun hz => hZ' (Finset.mem_coe.mpr hz)⟩
    · exact Or.inr ⟨h, fun hz => hZ' (Finset.mem_coe.mpr hz)⟩
  exact ⟨Z, f, hf₁, hf₂, D, ⟨hZT, hZna, hZfix, hZss⟩, hf0, hrf₁0, hrf₂0, hD, hDV₀1, hDpoleZ, htab₁, htab₂, hpat,
    fun V hne hDV hz₁ hz₂ => hcount V hne hDV (Finset.mem_coe.mpr hz₁) (Finset.mem_coe.mpr hz₂), hgoodT⟩

end AssemblyN

end MOVNCore

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    [CharP (ResidueField A) q] [IsAlgClosed (ResidueField A)] [DecidableEq (ResidueField A)]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ}
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))]
    [IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))]
    [IsCurveOver (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)]
    (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
    (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hqN : ¬ q ∣ N)

    (hcusp : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceFst V) → ProlongationTuple.IsCuspidal P V)
    (hsplit : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), ProlongationTuple.IsCuspidal P V →
      ProlongationTuple.IsInftySide P V ∨ ProlongationTuple.IsZeroSide P V)
    (hInftyNA : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), ProlongationTuple.IsInftySide P V → ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceFst V))
    (hInftyNA' : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), ProlongationTuple.IsInftySide P V → ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceSnd V))
    (hZeroNA : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), ProlongationTuple.IsZeroSide P V → ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceSnd V))
    (hZeroNA' : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), ProlongationTuple.IsZeroSide P V → ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceFst V))
    (hφaff : ∀ v : (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)), IsAffineGeomPlace (ResidueField A) N v → IsAffineGeomPlace (ResidueField A) N (frobOnPlacesGeomLevel (ResidueField A) N data hKr v))

    (hNss : ∀ s ∈ nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W, s.1 ∈ ssPlaces q N (ResidueField A) ∧ s.2 ∈ ssPlaces q N (ResidueField A))

    (hzone : ∀ T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)), (∀ t ∈ T, t ∉ ssPlaces q N (ResidueField A)) →
      ∃ Z : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)), (∀ v ∈ T, v ∈ Z) ∧ (∀ v ∈ T, frobOnPlacesGeomLevel (ResidueField A) N data hKr v ∈ Z) ∧ (∀ v, frobOnPlacesGeomLevel (ResidueField A) N data hKr v ∈ T → v ∈ Z) ∧
        (∀ v, ¬ IsAffineGeomPlace (ResidueField A) N v → v ∈ Z) ∧ (∀ v, frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr v) = v → v ∉ ssPlaces q N (ResidueField A) → v ∈ Z) ∧
        (∀ v ∈ Z, v ∉ ssPlaces q N (ResidueField A)))

    (hAUX : ∀ (B : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))) (m₁ m₂ : ℕ),
      ∃ (Q₁ : Fin m₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (Q₂ : Fin m₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
        (∀ i, P.IsStrictFst (Q₁ i)) ∧ (∀ j, P.IsStrictSnd (Q₂ j)) ∧
        (Function.Injective fun i => P.reduceFst (Q₁ i)) ∧ (Function.Injective fun j => P.reduceSnd (Q₂ j)) ∧
        (∀ i, P.reduceFst (Q₁ i) ∉ B) ∧ (∀ j, P.reduceSnd (Q₂ j) ∉ B))

    (hINTERP : ∀ (U Zv Za : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))) (t₀ : (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))) (β : (ResidueField A)) (val : (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)) → (ResidueField A)) (bad : Finset (ResidueField A)),
      Disjoint U Zv → Disjoint U Za → Disjoint Zv Za → t₀ ∉ U → t₀ ∉ Zv → t₀ ∉ Za →
      Zv.card + 2 * genusFF (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) + 2 ≤ U.card →
      ∃ g : ↥(modularFunctionFieldC (ResidueField A) N), g ∈ riemannRochSpace (∑ u ∈ U, Finsupp.single u (1 : ℤ)) ∧
        t₀.ord (g - algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) β) = 1 ∧ (∀ z ∈ Zv, z.HasValue g (val z)) ∧
        (∀ z ∈ Za, ∃ γ : (ResidueField A), γ ∉ bad ∧ z.HasValue g γ))

    (hREALN : ∀ (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), 0 ≤ D → P.IsGoodDiv D →
      2 * (genusFF (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) : ℤ) - 1 + W.card ≤ (Finsupp.mapDomain P.reduceFst (P.fstDiv D)).degree →
      2 * (genusFF (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) : ℤ) - 1 ≤ (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)).degree →
      ∀ (g₁ g₂ : ↥(modularFunctionFieldFullC (ResidueField A) N)),
        (R.ι g₁ : ↥(modularFunctionFieldC (ResidueField A) N)) ∈ riemannRochSpace (Finsupp.mapDomain P.reduceFst (P.fstDiv D)) →
        (R.ι g₂ : ↥(modularFunctionFieldC (ResidueField A) N)) ∈ riemannRochSpace (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)) →
        (∀ s ∈ nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W, ∃ c : (ResidueField A),
          s.1.HasValue (R.ι g₁ : ↥(modularFunctionFieldC (ResidueField A) N)) c ∧ s.2.HasValue (R.ι g₂ : ↥(modularFunctionFieldC (ResidueField A) N)) c) →
        ∃ (G : ↥(modularFunctionFieldBar (N * q))) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers),
          G ∈ riemannRochSpace D ∧ R.R₁.residue ⟨G, h₁⟩ = g₁ ∧ R.R₂.residue ⟨G, h₂⟩ = g₂)

    (toFull : ↥(modularFunctionFieldC (ResidueField A) N) → ↥(modularFunctionFieldFullC (ResidueField A) N)) (ι_toFull : ∀ g : ↥(modularFunctionFieldC (ResidueField A) N), R.ι (toFull g) = g)

    (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))) (hT : ∀ t ∈ T, t ∉ ssPlaces q N (ResidueField A))
    (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV₀ : P.reduceFst V₀ ∈ T ∨ P.reduceSnd V₀ ∈ T) :
    ∃ (Z : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))) (f : ↥(modularFunctionFieldBar (N * q))) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
      (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),

      ((∀ v ∈ T, v ∈ Z) ∧ (∀ v, ¬ IsAffineGeomPlace (ResidueField A) N v → v ∈ Z) ∧
        (∀ v, frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr v) = v → v ∉ ssPlaces q N (ResidueField A) → v ∈ Z) ∧ (∀ v ∈ Z, v ∉ ssPlaces q N (ResidueField A))) ∧
      f ≠ 0 ∧ R.residue₁ ⟨f, h₁⟩ ≠ 0 ∧ R.residue₂ ⟨f, h₂⟩ ≠ 0 ∧
      (∀ V, D V = V.ord f) ∧ D V₀ = 1 ∧
      (∀ V, D V < 0 → (P.IsStrictFst V ∧ P.reduceFst V ∉ Z) ∨ (P.IsStrictSnd V ∧ P.reduceSnd V ∉ Z)) ∧

      (∀ z, (z ∈ Z ∨ z ∈ W) → z ≠ P.reduceFst V₀ → z.ord (R.residue₁ ⟨f, h₁⟩) = 0) ∧
      (∀ z, (z ∈ Z ∨ z ∈ W) → z ≠ P.reduceSnd V₀ → z.ord (R.residue₂ ⟨f, h₂⟩) = 0) ∧
      (((P.reduceFst V₀).ord (R.residue₁ ⟨f, h₁⟩) = 1 ∧ (P.reduceSnd V₀).ord (R.residue₂ ⟨f, h₂⟩) = 0) ∨
        ((P.reduceFst V₀).ord (R.residue₁ ⟨f, h₁⟩) = 0 ∧ (P.reduceSnd V₀).ord (R.residue₂ ⟨f, h₂⟩) = 1)) ∧
      (∀ V, V ≠ V₀ → 1 ≤ D V → P.reduceFst V ∈ Z → P.reduceSnd V ∈ Z → False) ∧
      ∀ V ∈ D.support, V ≠ V₀ → P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T :=
  MOVNCore.coreN R hR hO W hW hRL hNV hqN hcusp hsplit hInftyNA hInftyNA' hZeroNA hZeroNA' hφaff hNss hzone hAUX hINTERP hREALN toFull ι_toFull T hT V₀ hV₀

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_ord_eq_one_orderTables_of_realisation
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_ord_eq_one_orderTables_of_realisation (solution)
