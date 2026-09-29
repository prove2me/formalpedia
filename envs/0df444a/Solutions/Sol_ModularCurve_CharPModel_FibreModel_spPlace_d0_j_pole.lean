-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.spPlace_d0_j_pole
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/f8486f6d-8c9d-5700-9bec-5d64b226d81a

import Definitions.Def_ModularCurve_SpecializationMap
import Theorems.Thm_ModularCurve_CharPModel_chart_dichotomy_jBar
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_j_pole
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

p2m_open "ModularCurve ModularCurve.CharPModel"
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_j_pole.AlgebraicCurve"
open IsLocalRing

set_option autoImplicit false

noncomputable section

noncomputable section

open IsLocalRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_inv"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg ord ord_inv exists_unit_mul_zpow algebraMap_mem' toValuationSubring mem_maximalIdeal_iff_ord_pos"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

private theorem _root_.AlgebraicCurve.Place.algebraMap_mem (a : K) : algebraMap K F a ∈ w.toValuationSubring := w.algebraMap_mem' a

p2m_export "AlgebraicCurve.Place" "algebraMap_mem"

private theorem _root_.AlgebraicCurve.Place.algebraMap_mem_nonunits_iff (a : K) :
    algebraMap K F a ∈ w.toValuationSubring.nonunits ↔ a = 0 := by
  constructor
  · intro h
    rcases (ValuationSubring.mem_nonunits_iff_or _).mp h with h0 | hinv
    · exact (map_eq_zero _).mp h0
    · exact absurd (by simpa using w.algebraMap_mem a⁻¹) hinv
  · rintro rfl
    simp [ZeroMemClass.zero_mem]

p2m_export "AlgebraicCurve.Place" "algebraMap_mem_nonunits_iff"

private theorem _root_.AlgebraicCurve.Place.mul_mem_nonunits {x y : F} (hx : x ∈ w.toValuationSubring.nonunits)
    (hy : y ∈ w.toValuationSubring) : x * y ∈ w.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
  rw [← ValuationSubring.valuation_le_one_iff] at hy
  calc w.toValuationSubring.valuation (x * y)
      = w.toValuationSubring.valuation x * w.toValuationSubring.valuation y := map_mul _ _ _
    _ ≤ w.toValuationSubring.valuation x * 1 := by gcongr
    _ = w.toValuationSubring.valuation x := mul_one _
    _ < 1 := hx

p2m_export "AlgebraicCurve.Place" "mul_mem_nonunits"

private theorem _root_.AlgebraicCurve.Place.mem_of_ord_pos {f : F} (h : 0 < w.ord f) : f ∈ w.toValuationSubring := by
  have hf : f ≠ 0 := by rintro rfl; simp at h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf hπ
  rw [hu, show w.ord f = (((w.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h.le).symm,
    zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem (π : w.toValuationSubring).2 _)

p2m_export "AlgebraicCurve.Place" "mem_of_ord_pos"

private theorem _root_.AlgebraicCurve.Place.mem_nonunits_iff_ord_pos {f : F} (hf : f ≠ 0) :
    f ∈ w.toValuationSubring.nonunits ↔ 0 < w.ord f := by
  constructor
  · intro h
    have hmem : f ∈ w.toValuationSubring := w.toValuationSubring.nonunits_subset h
    have h' : ((⟨f, hmem⟩ : w.toValuationSubring) : F) ∈ w.toValuationSubring.nonunits := h
    rw [ValuationSubring.coe_mem_nonunits_iff] at h'
    exact (w.mem_maximalIdeal_iff_ord_pos hf hmem).mp h'
  · intro h
    have hmem : f ∈ w.toValuationSubring := w.mem_of_ord_pos h
    have h' := (w.mem_maximalIdeal_iff_ord_pos hf hmem).mpr h
    rw [← ValuationSubring.coe_mem_nonunits_iff] at h'
    exact h'

p2m_export "AlgebraicCurve.Place" "mem_nonunits_iff_ord_pos"

private def _root_.AlgebraicCurve.Place.HasValueAt (f : F) (a : K) : Prop :=
  f - algebraMap K F a ∈ w.toValuationSubring.nonunits

p2m_export "AlgebraicCurve.Place" "HasValueAt"
private theorem hasValueAt_iff (f : F) (a : K) :
    w.HasValueAt f a ↔ f - algebraMap K F a ∈ w.toValuationSubring.nonunits := Iff.rfl

private theorem _root_.AlgebraicCurve.Place.hasValueAt_iff_ord_pos {f : F} {a : K} (h : f ≠ algebraMap K F a) :
    w.HasValueAt f a ↔ 0 < w.ord (f - algebraMap K F a) :=
  w.mem_nonunits_iff_ord_pos (sub_ne_zero.mpr h)

p2m_export "AlgebraicCurve.Place" "hasValueAt_iff_ord_pos"
private theorem hasValueAt_of_ord_pos {f : F} {a : K} (h : 0 < w.ord (f - algebraMap K F a)) :
    w.HasValueAt f a := by
  have hne : f ≠ algebraMap K F a := by
    intro hfa; rw [hfa, sub_self] at h; simp at h
  exact (w.hasValueAt_iff_ord_pos hne).mpr h

private theorem _root_.AlgebraicCurve.Place.hasValueAt_algebraMap (a : K) : w.HasValueAt (algebraMap K F a) a := by
  simp [HasValueAt, ZeroMemClass.zero_mem]

p2m_export "AlgebraicCurve.Place" "hasValueAt_algebraMap"

private theorem _root_.AlgebraicCurve.Place.hasValueAt_zero_iff (f : F) : w.HasValueAt f 0 ↔ f ∈ w.toValuationSubring.nonunits := by
  simp [HasValueAt]

p2m_export "AlgebraicCurve.Place" "hasValueAt_zero_iff"

private theorem _root_.AlgebraicCurve.Place.mem_of_hasValueAt {f : F} {a : K} (h : w.HasValueAt f a) : f ∈ w.toValuationSubring := by
  have h1 : f - algebraMap K F a ∈ w.toValuationSubring := w.toValuationSubring.nonunits_subset h
  simpa using add_mem h1 (w.algebraMap_mem a)

p2m_export "AlgebraicCurve.Place" "mem_of_hasValueAt"
namespace HasValueAt
p2m_open_scoped "AlgebraicCurve.Place.HasValueAt" in
variable {w} in

private theorem _root_.AlgebraicCurve.Place.HasValueAt.unique {f : F} {a b : K} (ha : w.HasValueAt f a) (hb : w.HasValueAt f b) :
    a = b := by
  have h : algebraMap K F (a - b) ∈ w.toValuationSubring.nonunits := by
    have := sub_mem hb ha
    rwa [sub_sub_sub_cancel_left, ← map_sub] at this
  exact sub_eq_zero.mp ((w.algebraMap_mem_nonunits_iff _).mp h)

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.unique"
namespace HasValueAt
p2m_open_scoped "AlgebraicCurve.Place.HasValueAt" in
variable {w} in
private theorem _root_.AlgebraicCurve.Place.HasValueAt.add {f g : F} {a b : K} (hf : w.HasValueAt f a) (hg : w.HasValueAt g b) :
    w.HasValueAt (f + g) (a + b) := by
  have := add_mem hf hg
  rw [HasValueAt, map_add]
  convert this using 1
  ring

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.add"
namespace HasValueAt
p2m_open_scoped "AlgebraicCurve.Place.HasValueAt" in
variable {w} in
private theorem _root_.AlgebraicCurve.Place.HasValueAt.neg {f : F} {a : K} (hf : w.HasValueAt f a) : w.HasValueAt (-f) (-a) := by
  have := neg_mem hf
  rw [HasValueAt, map_neg]
  convert this using 1
  ring

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.neg"
namespace HasValueAt
p2m_open_scoped "AlgebraicCurve.Place.HasValueAt" in
variable {w} in
private theorem _root_.AlgebraicCurve.Place.HasValueAt.mul {f g : F} {a b : K} (hf : w.HasValueAt f a) (hg : w.HasValueAt g b) :
    w.HasValueAt (f * g) (a * b) := by
  have h1 : (f - algebraMap K F a) * g ∈ w.toValuationSubring.nonunits :=
    w.mul_mem_nonunits hf (w.mem_of_hasValueAt hg)
  have h2 : (g - algebraMap K F b) * algebraMap K F a ∈ w.toValuationSubring.nonunits :=
    w.mul_mem_nonunits hg (w.algebraMap_mem a)
  have := add_mem h1 h2
  rw [HasValueAt, map_mul]
  convert this using 1
  ring

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.mul"
namespace HasValueAt
p2m_open_scoped "AlgebraicCurve.Place.HasValueAt" in
variable {w} in

private theorem _root_.AlgebraicCurve.Place.HasValueAt.inv {f : F} {a : K} (hf : w.HasValueAt f a) (ha : a ≠ 0) :
    w.HasValueAt f⁻¹ a⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    have : w.HasValueAt (0 : F) 0 := by simpa using w.hasValueAt_algebraMap 0
    exact ha (hf.unique this)
  have hfu : f ∉ w.toValuationSubring.nonunits := fun hfn =>
    ha (hf.unique ((w.hasValueAt_zero_iff f).mpr hfn))
  have hfinv : f⁻¹ ∈ w.toValuationSubring := by
    by_contra hne
    exact hfu ((ValuationSubring.mem_nonunits_iff_or _).mpr (Or.inr (by simpa using hne)))
  have hprod : (f - algebraMap K F a) * (f⁻¹ * algebraMap K F a⁻¹)
      ∈ w.toValuationSubring.nonunits :=
    w.mul_mem_nonunits hf (mul_mem hfinv (w.algebraMap_mem _))
  have := neg_mem hprod
  change f⁻¹ - algebraMap K F a⁻¹ ∈ w.toValuationSubring.nonunits
  convert this using 1
  have haF : algebraMap K F a ≠ 0 := by simpa using ha
  rw [map_inv₀]
  field_simp
  ring

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.inv"
namespace HasValueAt
p2m_open_scoped "AlgebraicCurve.Place.HasValueAt" in
variable {w} in

private theorem _root_.AlgebraicCurve.Place.HasValueAt.div {f g : F} {a b : K} (hf : w.HasValueAt f a) (hg : w.HasValueAt g b)
    (hb : b ≠ 0) : w.HasValueAt (f / g) (a / b) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact hf.mul (hg.inv hb)

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.div"

private theorem _root_.AlgebraicCurve.Place.hasValueAt_iff_residue {f : F} (hf : f ∈ w.toValuationSubring) (a : K) :
    w.HasValueAt f a ↔
      residue w.toValuationSubring ⟨f, hf⟩ = algebraMap K w.ResidueField a := by
  have e : algebraMap K w.ResidueField a =
      residue w.toValuationSubring (algebraMap K w.toValuationSubring a) := rfl
  rw [e, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

p2m_export "AlgebraicCurve.Place" "hasValueAt_iff_residue"

private theorem exists_hasValueAt (hw : Function.Surjective (algebraMap K w.ResidueField)) {f : F}
    (hf : f ∈ w.toValuationSubring) : ∃ a : K, w.HasValueAt f a := by
  obtain ⟨a, ha⟩ := hw (residue w.toValuationSubring ⟨f, hf⟩)
  exact ⟨a, (w.hasValueAt_iff_residue hf a).mpr ha.symm⟩

private theorem _root_.AlgebraicCurve.Place.surjective_algebraMap_residueField_of_isAlgClosed [IsAlgClosed K]
    [Module.Finite K w.ResidueField] : Function.Surjective (algebraMap K w.ResidueField) :=
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K w.ResidueField
  (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

p2m_export "AlgebraicCurve.Place" "surjective_algebraMap_residueField_of_isAlgClosed"

private theorem surjective_algebraMap_residueField_of_deg_eq_one [IsAlgClosed K] (h : w.deg = 1) :
    Function.Surjective (algebraMap K w.ResidueField) :=
  haveI : Module.Finite K w.ResidueField := Module.finite_of_finrank_eq_succ (n := 0) h
  w.surjective_algebraMap_residueField_of_isAlgClosed

end Place
end AlgebraicCurve
end

namespace SolWork

private theorem jBar_sub_const_ne (N : ℕ) [NeZero N] (c : AlgebraicClosure ℚ) :
    (ModularCurve.CharPModel.jBar N : laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionFieldFull N))
      - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionFieldFull N)) c ≠ 0 := by
  intro h0
  apply ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N
  have halg : IsAlgebraic (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar N) := by
    have : (ModularCurve.CharPModel.jBar N : laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionFieldFull N))
        = algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionFieldFull N)) c := by
      have := sub_eq_zero.mp h0
      exact this
    rw [this]
    exact isAlgebraic_algebraMap c
  exact halg

private theorem jLine_ne_zero (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ≠ 0 := by
  intro h0
  apply ModularCurve.transcendental_jqModC k
  have hval : jqModC k = 0 := congrArg Subtype.val h0
  exact hval ▸ isAlgebraic_zero

end SolWork

open SolWork in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (k : Type*)
    [Field k] [CharP k ℓ] (red : A →+* k)
    (fm : ModularCurve.CharPModel.FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
    (∀ a : A,
      w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) →
    ((fm.spPlace hred dataAll hsep) w).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
        < 0 := by
  intro w hpole

  rcases ModularCurve.CharPModel.chart_dichotomy_jBar N A dataAll w with ⟨a, ha⟩ | ⟨a, ha⟩
  · exfalso
    have hne := jBar_sub_const_ne N (a : AlgebraicClosure ℚ)
    have hpos := (w.mem_nonunits_iff_ord_pos hne).mp ha
    exact absurd hpos (not_lt.mpr (hpole a))

  · have hjne : (ModularCurve.CharPModel.jBar N : laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionFieldFull N)) ≠ 0 := by
      have := jBar_sub_const_ne N 0
      simpa using this
    have ha𝔪 : (a : A) ∈ IsLocalRing.maximalIdeal A := by
      by_contra hunit
      have hu : IsUnit (a : A) := IsLocalRing.notMem_maximalIdeal.mp hunit
      obtain ⟨u, hu_eq⟩ := hu
      have hane : (a : AlgebraicClosure ℚ) ≠ 0 := by
        intro h0
        apply hunit
        have : (a : A) = 0 := Subtype.ext h0
        rw [this]
        exact (IsLocalRing.maximalIdeal A).zero_mem

      have hinv_mem : ((a : AlgebraicClosure ℚ))⁻¹ ∈ A := by
        have : ((u⁻¹ : Aˣ) : A) * (a : A) = 1 := by
          rw [← hu_eq]
          exact u.inv_mul
        have hcoe : (((u⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) * (a : AlgebraicClosure ℚ) = 1 := by
          exact_mod_cast congrArg (algebraMap A (AlgebraicClosure ℚ)) this
        have : (((u⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) = ((a : AlgebraicClosure ℚ))⁻¹ :=
          eq_inv_of_mul_eq_one_left hcoe
        rw [← this]
        exact ((u⁻¹ : Aˣ) : A).2

      have hval : w.HasValueAt
          (ModularCurve.CharPModel.jBar N : laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionFieldFull N)) ((a : AlgebraicClosure ℚ))⁻¹ := by
        have hv : w.HasValueAt
            ((ModularCurve.CharPModel.jBar N : laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionFieldFull N))⁻¹) (a : AlgebraicClosure ℚ) := ha
        have := hv.inv hane
        simpa [inv_inv] using this
      have hne := jBar_sub_const_ne N ((a : AlgebraicClosure ℚ))⁻¹
      have hpos := (w.mem_nonunits_iff_ord_pos hne).mp hval
      exact absurd hpos (not_lt.mpr (hpole ⟨_, hinv_mem⟩))

    have hdict := (fm.piInf_mem_spPlace_nonunits_iff hred dataAll hsep w hpole
        ⟨(ModularCurve.CharPModel.jBar N)⁻¹, fm.jInvBar_mem⟩).mpr ⟨a, ha𝔪, ha⟩
    rw [fm.piInf_jInv] at hdict

    have hlne := jLine_ne_zero k N
    have hpos := ((fm.spPlace hred dataAll hsep w).mem_nonunits_iff_ord_pos
      (inv_ne_zero hlne)).mp hdict
    have hoinv := AlgebraicCurve.Place.ord_inv
      (v := fm.spPlace hred dataAll hsep w)
      (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
    rw [hoinv] at hpos
    linarith

end
end S_ModularCurve_CharPModel_FibreModel_spPlace_d0_j_pole
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_j_pole (solution)
