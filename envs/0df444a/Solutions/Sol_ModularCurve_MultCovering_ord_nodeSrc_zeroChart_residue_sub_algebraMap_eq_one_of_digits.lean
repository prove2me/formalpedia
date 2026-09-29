-- Prove2me | solution 1 for ModularCurve.MultCovering.ord_nodeSrc_zeroChart_residue_sub_algebraMap_eq_one_of_digits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/3e16abb1-d7a6-51b1-be1f-9b098c2694ea

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Theorems.Thm_AlgebraicCurve_Place_hasValue_iff_mem_and_eq_or_ord_sub_pos
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_ord_nodeSrc_zeroChart_residue_sub_algebraMap_eq_one_of_digits
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

namespace P2MF2J

open AlgebraicCurve ModularCurve Polynomial IsLocalRing

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ne_zero_of_ord_ne_zero (v : Place K F) {g : F} (h : v.ord g ≠ 0) : g ≠ 0 := by
  rintro rfl
  exact h (Place.ord_zero v)

theorem ord_algebraMap' (v : Place K F) {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 :=
  (Place.hasValue_algebraMap v c).ord_eq_zero hc

namespace HasValue

private theorem _root_.P2MF2J.HasValue.add {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

end HasValue
p2m_export "P2MF2J" "HasValue.add"
end PlaceFacts

section JLine

variable (k : Type*) [Field k] [DecidableEq k]

noncomputable abbrev jB : ↥(modularFunctionFieldC k 1) := ⟨jqModC k, jqModC_mem k 1⟩

end JLine

end P2MF2J

namespace P2MW8

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering Polynomial

section Values

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hasValue_evalAt (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.HasValue f (v.evalAt f) :=
  ⟨hf, (v.algebraMap_evalAt hv hf).symm⟩

theorem hasValue_zero (v : Place K F) : v.HasValue (0 : F) 0 := by
  simpa using Place.hasValue_algebraMap v (0 : K)

theorem hasValue_const_smul {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) (c : K) :
    v.HasValue (c • g) (c * a) := by
  rw [Algebra.smul_def]; exact (Place.hasValue_algebraMap v c).mul h

theorem hasValue_neg {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) : v.HasValue (-g) (-a) := by
  have := hasValue_const_smul h (-1)
  simpa using this

theorem hasValue_sub {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  have := P2MF2J.HasValue.add h (hasValue_neg h')
  simpa [sub_eq_add_neg] using this

theorem hasValue_sum {v : Place K F} {ι : Type*} (s : Finset ι) (g : ι → F) (a : ι → K)
    (h : ∀ i ∈ s, v.HasValue (g i) (a i)) : v.HasValue (∑ i ∈ s, g i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasValue_zero v
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    exact P2MF2J.HasValue.add (h b (Finset.mem_insert_self b s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ord_eq_zero_iff_value_ne_zero {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) (hg : g ≠ 0) :
    v.ord g = 0 ↔ a ≠ 0 := by
  constructor
  · intro h0 ha
    subst ha
    rw [Place.hasValue_iff_mem_and_eq_or_ord_sub_pos, map_zero, sub_zero] at h
    rcases h.2 with h1 | h1
    · exact hg h1
    · omega
  · exact h.ord_eq_zero

theorem ord_sub_pos_of_hasValue {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) (hne : g ≠ algebraMap K F a) :
    0 < v.ord (g - algebraMap K F a) := by
  rw [Place.hasValue_iff_mem_and_eq_or_ord_sub_pos] at h
  rcases h.2 with h1 | h1
  · exact absurd h1 hne
  · exact h1

end Values

section JLineDeriv

variable (k : Type*) [Field k] [DecidableEq k]

def HasDerivVal (x : k) (g : ↥(modularFunctionFieldC k 1)) (a w : k) : Prop :=
  (charLGeomPlaceOfPoint k x).HasValue g a ∧
    (charLGeomPlaceOfPoint k x).HasValue
      ((g - algebraMap k _ a) * (P2MF2J.jB k - algebraMap k _ x)⁻¹) w

variable {k}

theorem jB_sub_ne_zero (x : k) : P2MF2J.jB k - algebraMap k ↥(modularFunctionFieldC k 1) x ≠ 0 := by
  intro h0
  have h1 := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k x x
  rw [if_pos rfl] at h1
  change (charLGeomPlaceOfPoint k x).ord (P2MF2J.jB k - algebraMap k _ x) = 1 at h1
  rw [h0, Place.ord_zero] at h1
  exact zero_ne_one h1

theorem ord_jB_sub_self (x : k) :
    (charLGeomPlaceOfPoint k x).ord (P2MF2J.jB k - algebraMap k ↥(modularFunctionFieldC k 1) x) = 1 := by
  have h1 := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k x x
  rw [if_pos rfl] at h1
  exact h1

theorem HasDerivVal.add {x : k} {g g' : ↥(modularFunctionFieldC k 1)} {a w a' w' : k}
    (h : HasDerivVal k x g a w) (h' : HasDerivVal k x g' a' w') : HasDerivVal k x (g + g') (a + a') (w + w') := by
  refine ⟨P2MF2J.HasValue.add h.1 h'.1, ?_⟩
  have e : (g + g' - algebraMap k _ (a + a')) * (P2MF2J.jB k - algebraMap k _ x)⁻¹
      = (g - algebraMap k _ a) * (P2MF2J.jB k - algebraMap k _ x)⁻¹
        + (g' - algebraMap k _ a') * (P2MF2J.jB k - algebraMap k _ x)⁻¹ := by
    rw [map_add]; ring
  rw [e]
  exact P2MF2J.HasValue.add h.2 h'.2

theorem HasDerivVal.smul {x : k} {g : ↥(modularFunctionFieldC k 1)} {a w : k}
    (h : HasDerivVal k x g a w) (c : k) : HasDerivVal k x (c • g) (c * a) (c * w) := by
  refine ⟨hasValue_const_smul h.1 c, ?_⟩
  have e : (c • g - algebraMap k _ (c * a)) * (P2MF2J.jB k - algebraMap k _ x)⁻¹
      = c • ((g - algebraMap k _ a) * (P2MF2J.jB k - algebraMap k _ x)⁻¹) := by
    rw [map_mul, Algebra.smul_def, Algebra.smul_def]; ring
  rw [e]
  exact hasValue_const_smul h.2 c

theorem hasDerivVal_sum {x : k} {ι : Type*} (s : Finset ι) (g : ι → ↥(modularFunctionFieldC k 1)) (a w : ι → k)
    (h : ∀ i ∈ s, HasDerivVal k x (g i) (a i) (w i)) :
    HasDerivVal k x (∑ i ∈ s, g i) (∑ i ∈ s, a i) (∑ i ∈ s, w i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨hasValue_zero _, ?_⟩
    rw [map_zero, sub_zero, zero_mul]; exact hasValue_zero _
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, Finset.sum_insert hb]
    exact (h b (Finset.mem_insert_self b s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem HasDerivVal.ord_sub_eq_one_iff {x : k} {g : ↥(modularFunctionFieldC k 1)} {a w : k}
    (h : HasDerivVal k x g a w) (hne : g ≠ algebraMap k _ a) :
    (charLGeomPlaceOfPoint k x).ord (g - algebraMap k _ a) = 1 ↔ w ≠ 0 := by
  have hu : P2MF2J.jB k - algebraMap k ↥(modularFunctionFieldC k 1) x ≠ 0 := jB_sub_ne_zero x
  have hga : g - algebraMap k _ a ≠ 0 := sub_ne_zero.mpr hne
  have hq : (g - algebraMap k _ a) * (P2MF2J.jB k - algebraMap k ↥(modularFunctionFieldC k 1) x)⁻¹ ≠ 0 :=
    mul_ne_zero hga (inv_ne_zero hu)
  have key := ord_eq_zero_iff_value_ne_zero h.2 hq
  have e1 : g - algebraMap k _ a = ((g - algebraMap k _ a) * (P2MF2J.jB k - algebraMap k ↥(modularFunctionFieldC k 1) x)⁻¹)
      * (P2MF2J.jB k - algebraMap k ↥(modularFunctionFieldC k 1) x) := by
    rw [mul_assoc, inv_mul_cancel₀ hu, mul_one]
  have e2 : (charLGeomPlaceOfPoint k x).ord (g - algebraMap k _ a)
      = (charLGeomPlaceOfPoint k x).ord ((g - algebraMap k _ a) * (P2MF2J.jB k - algebraMap k ↥(modularFunctionFieldC k 1) x)⁻¹) + 1 := by
    conv_lhs => rw [e1]
    rw [(charLGeomPlaceOfPoint k x).ord_mul hq hu, ord_jB_sub_self x]
  rw [e2]
  constructor
  · intro h1
    exact key.mp (by omega)
  · intro hw
    rw [key.mpr hw]
    norm_num

end JLineDeriv

end P2MW8

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering P2MW8 in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (d : Fin r → Fin r → ZMod p)
    (g' : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hint' : ∀ l, g' l ∈ (zeroChart Γ).integers)
    (hres0 : ∀ i : Fin r, (zeroChart Γ).residue ⟨g' i, hint' i⟩
      = ∑ j : Fin r, algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)
          (if hasseExp Φ.toFamData j ≤ hasseExp Φ.toFamData i then ((d i j).val : ResidueField ↥A) else 0)
          * (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩)
    (e : Fin (mAnnuli p)) (he : jWidth (ssValue Γ e) = 3)

    (a w : Fin r → ResidueField ↥A)
    (ha : ∀ j : Fin r, hasseExp Φ.toFamData j ≤ 1 →
      (nodeSrc Γ e).HasValue ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩) (a j))
    (hw : ∀ j : Fin r, hasseExp Φ.toFamData j ≤ 1 →
      (nodeSrc Γ e).HasValue
        (((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩
            - algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) (a j))
          * ((⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) 1⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) 1))
              - algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) (ssValue Γ e ^ p))⁻¹)
        (w j))

    (hunr : ∀ i : Fin r, 1 ≤ (i : ℕ) → hasseExp Φ.toFamData i = 1 →
      (∑ j : Fin r, (if hasseExp Φ.toFamData j ≤ hasseExp Φ.toFamData i then ((d i j).val : ResidueField ↥A) else 0)
        * w j) ≠ 0) :
    ∀ i : Fin r, 1 ≤ (i : ℕ) → hasseExp Φ.toFamData i = 1 →
      ∃ c : ResidueField ↥A,
        (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨g' i, hint' i⟩
          - algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) c) = 1 := by
  intro i hi hni
  have hplace : nodeSrc Γ e = charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e ^ p) := rfl
  let ρ : Fin r → ↥(modularFunctionFieldC (ResidueField ↥A) 1) :=
    fun j => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩
  let κ : Fin r → ResidueField ↥A :=
    fun j => if hasseExp Φ.toFamData j ≤ hasseExp Φ.toFamData i then ((d i j).val : ResidueField ↥A) else 0

  have hsum : (zeroChart Γ).residue ⟨g' i, hint' i⟩ = ∑ j, κ j • ρ j := by
    rw [hres0 i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]

  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin r)),
      HasDerivVal (ResidueField ↥A) (ssValue Γ e ^ p) (κ j • ρ j) (κ j * a j) (κ j * w j) := by
    intro j _
    by_cases hj : hasseExp Φ.toFamData j ≤ hasseExp Φ.toFamData i
    · have hj1 : hasseExp Φ.toFamData j ≤ 1 := hni ▸ hj
      have hd : HasDerivVal (ResidueField ↥A) (ssValue Γ e ^ p) (ρ j) (a j) (w j) :=
        ⟨hplace ▸ ha j hj1, hplace ▸ hw j hj1⟩
      exact hd.smul (κ j)
    · have hκ0 : κ j = 0 := if_neg hj
      rw [hκ0, zero_smul, zero_mul, zero_mul]
      refine ⟨hasValue_zero _, ?_⟩
      rw [map_zero, sub_zero, zero_mul]; exact hasValue_zero _
  have hD : HasDerivVal (ResidueField ↥A) (ssValue Γ e ^ p) (∑ j, κ j • ρ j) (∑ j, κ j * a j) (∑ j, κ j * w j) :=
    hasDerivVal_sum Finset.univ _ _ _ hterm
  have hW : (∑ j, κ j * w j) ≠ 0 := hunr i hi hni
  refine ⟨∑ j, κ j * a j, ?_⟩
  rw [hplace, hsum]

  have hne : (∑ j, κ j • ρ j) ≠ algebraMap (ResidueField ↥A) _ (∑ j, κ j * a j) := by
    intro heq
    apply hW
    have h2 := hD.2
    rw [heq, sub_self, zero_mul] at h2
    rw [Place.hasValue_iff_mem_and_eq_or_ord_sub_pos] at h2
    rcases h2.2 with h3 | h3
    · have : algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) (∑ j, κ j * w j) = 0 := h3.symm
      exact (map_eq_zero _).mp this
    · exfalso
      rw [zero_sub, ← map_neg, Place.ord_algebraMap] at h3
      exact lt_irrefl _ h3
  exact (hD.ord_sub_eq_one_iff hne).mpr hW

end S_ModularCurve_MultCovering_ord_nodeSrc_zeroChart_residue_sub_algebraMap_eq_one_of_digits
end P2MW
export P2MW.S_ModularCurve_MultCovering_ord_nodeSrc_zeroChart_residue_sub_algebraMap_eq_one_of_digits (solution)
