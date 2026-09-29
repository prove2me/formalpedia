-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.spPlace_d0_j
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/6ec853b6-9a42-5486-a2c3-625d060c343f

import Definitions.Def_ModularCurve_SpecializationMap
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_j
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

p2m_open "ModularCurve ModularCurve.CharPModel"
open Polynomial
open IsLocalRing

namespace ValuationSubring
p2m_export "ValuationSubring" "comap subtype coe_mem_nonunits_iff neg_mem ext mem_nonunits_iff_or zero_mem nonunits mem_nonunits_iff mul_mem nonunits_subset add_mem valuation_le_one_iff valuation inclusion"
p2m_open "ValuationSubring"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (A : ValuationSubring K)

private theorem closureConstantsAdjoin_eq_range_aeval (x : F) :
    Subring.closure (Set.range ((algebraMap K F).comp A.subtype) ∪ {x}) =
      (aeval (R := A) x).toRingHom.range := by
  apply le_antisymm
  · rw [Subring.closure_le]
    rintro y (⟨a, rfl⟩ | rfl)
    · refine ⟨C a, ?_⟩
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, RingHom.coe_comp,
        Function.comp_apply]
      rfl
    · exact ⟨X, by simp⟩
  · rintro y ⟨p, rfl⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    induction p using Polynomial.induction_on with
    | C a =>
      rw [aeval_C]
      exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
    | add p q hp hq =>
      rw [map_add]
      exact Subring.add_mem _ hp hq
    | monomial n a h =>
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
      exact Subring.mul_mem _ h (Subring.subset_closure (Or.inr rfl))

private theorem _root_.ValuationSubring.aeval_injective_of_transcendental {x : F} (hx : Transcendental K x) :
    Function.Injective (aeval (R := A) x) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hK : aeval x (p.map (algebraMap A K)) = 0 := by rwa [aeval_map_algebraMap]
  have hp' : p.map (algebraMap A K) = 0 :=
    (injective_iff_map_eq_zero _).mp (transcendental_iff_injective.mp hx) _ hK
  exact (Polynomial.map_injective (algebraMap A K) Subtype.val_injective)
    (by rw [hp', Polynomial.map_zero])

p2m_export "ValuationSubring" "aeval_injective_of_transcendental"

private theorem _root_.ValuationSubring.aeval_mem_closure (x : F) (p : A[X]) :
    aeval x p ∈ Subring.closure (Set.range ((algebraMap K F).comp A.subtype) ∪ {x}) := by
  rw [closureConstantsAdjoin_eq_range_aeval]
  exact ⟨p, rfl⟩

p2m_export "ValuationSubring" "aeval_mem_closure"

private noncomputable def _root_.ValuationSubring.polynomialEquivClosure {x : F} (hx : Transcendental K x) :
    A[X] ≃+* Subring.closure (Set.range ((algebraMap K F).comp A.subtype) ∪ {x}) :=
  RingEquiv.ofBijective
    ((aeval (R := A) x).toRingHom.codRestrict _ (A.aeval_mem_closure x))
    ⟨fun p q h => A.aeval_injective_of_transcendental hx (Subtype.ext_iff.mp h),
      fun y => by
        obtain ⟨p, hp⟩ : (y : F) ∈ (aeval (R := A) x).toRingHom.range := by
          rw [← closureConstantsAdjoin_eq_range_aeval]
          exact y.2
        exact ⟨p, Subtype.ext hp⟩⟩

p2m_export "ValuationSubring" "polynomialEquivClosure"
@[scoped simp]
private theorem polynomialEquivClosure_apply {x : F} (hx : Transcendental K x) (p : A[X]) :
    (A.polynomialEquivClosure hx p : F) = aeval x p := rfl

private theorem isIntegrallyClosed_closure {x : F} (hx : Transcendental K x) :
    IsIntegrallyClosed (Subring.closure (Set.range ((algebraMap K F).comp A.subtype) ∪ {x})) :=
  IsIntegrallyClosed.of_equiv (A.polynomialEquivClosure hx)

end ValuationSubring
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_j.ValuationSubring"

namespace Subring
p2m_export "Subring" "inclusion subtype ext subset_closure map closure_le closure comap"
p2m_open "Subring"

variable {F : Type*} [Field F]

private theorem isIntegral_iff_exists_monic_eval₂ (S : Subring F) (b : F) :
    IsIntegral S b ↔ ∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype b p = 0 :=
  Iff.rfl

private theorem exists_ideal_le_comap_eq_of_isIntegral {S B : Subring F} (hSB : S ≤ B)
    [IsIntegrallyClosed S] (hint : ∀ b : B, IsIntegral S (b : F))
    {p q : Ideal S} [p.IsPrime] [q.IsPrime] (hpq : p ≤ q)
    (Q : Ideal B) [Q.IsPrime] (hQ : Q.comap (Subring.inclusion hSB) = q) :
    ∃ P : Ideal B, P ≤ Q ∧ P.IsPrime ∧ P.comap (Subring.inclusion hSB) = p := by
  letI : Algebra S B := (Subring.inclusion hSB).toAlgebra
  have halg : ∀ s : S, algebraMap S B s = Subring.inclusion hSB s := fun _ => rfl
  haveI : FaithfulSMul S B := (faithfulSMul_iff_algebraMap_injective S B).mpr fun a b h => by
    rw [halg, halg] at h
    have h' : (a : F) = (b : F) := congrArg (fun y : B => (y : F)) h
    exact Subtype.ext h'
  haveI : Algebra.IsIntegral S B := ⟨fun b => by
    obtain ⟨f, hf, hfb⟩ := hint b
    refine ⟨f, hf, ?_⟩
    apply Subtype.val_injective
    change B.subtype (Polynomial.eval₂ (algebraMap S B) b f) = ((0 : B) : F)
    have hc : B.subtype.comp (algebraMap S B) = S.subtype := RingHom.ext fun _ => rfl
    rw [Polynomial.hom_eval₂, hc]
    exact hfb⟩
  haveI : Q.LiesOver q := ⟨by rw [Ideal.under_def, ← hQ]; rfl⟩
  obtain ⟨P, hPQ, hP, hPp⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := q) Q hpq
  exact ⟨P, hPQ, hP, by rw [hPp.over, Ideal.under_def]; rfl⟩

end Subring
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_j.ValuationSubring"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg ord exists_unit_mul_zpow algebraMap_mem' toValuationSubring mem_maximalIdeal_iff_ord_pos"
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
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_j.ValuationSubring"
end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_j.ValuationSubring"

open _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_j.AlgebraicCurve in
private theorem transcendental_subtype {K L : Type*} [Field K] [Field L] [Algebra K L]
    (S : IntermediateField K L) {x : L} (hx : x ∈ S) (h : Transcendental K x) :
    Transcendental K (⟨x, hx⟩ : S) := by
  intro halg
  apply h
  obtain ⟨p, hp0, hp⟩ := halg
  refine ⟨p, hp0, ?_⟩
  have h2 := congrArg S.val hp
  rw [map_zero, ← Polynomial.aeval_algHom_apply] at h2
  simpa using h2

private theorem transcendental_jC (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Transcendental k (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) :=
  transcendental_subtype _ (jqModC_mem k N) (ModularCurve.transcendental_jqModC k)

private theorem ne_const_of_transcendental {K L : Type*} [Field K] [Field L] [Algebra K L]
    {x : L} (h : Transcendental K x) (c : K) : x ≠ algebraMap K L c := fun he =>
  h (he ▸ isAlgebraic_algebraMap c)

open _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_j.AlgebraicCurve in
theorem solution (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (k : Type*)
    [Field k] [CharP k ℓ] (red : A →+* k)
    (fm : ModularCurve.CharPModel.FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∀ a : A,
    0 < w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) →
    0 < ((fm.spPlace hred dataAll hsep) w).ord
        (⟨jqModC k, jqModC_mem k N⟩ - algebraMap k (modularFunctionFieldC k N) (red a)) := by
  intro w a ha
  classical
  set jel : fm.BFin := ⟨jBar N, fm.jBar_mem⟩ with hjel
  set cel : fm.BFin := ⟨constantsHom N A a, fm.constFin_mem a⟩ with hcel
  have hπ : (fm.piFin (jel - cel) : modularFunctionFieldC k N)
      = (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
        - algebraMap k (modularFunctionFieldC k N) (red a) := by
    rw [map_sub, fm.piFin_j, fm.piFin_const]
  have hup : ((jel - cel : fm.BFin) : laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionFieldFull N))
      - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionFieldFull N)) ((0 : A) : AlgebraicClosure ℚ)
      ∈ w.toValuationSubring.nonunits := by
    have hne : (jBar N : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionFieldFull N)) (a : AlgebraicClosure ℚ) ≠ 0 :=
      sub_ne_zero.mpr
        (ne_const_of_transcendental (ModularCurve.transcendental_coeffEmb_jq _ N) _)
    have h0 : ((jel - cel : fm.BFin) : laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionFieldFull N)) ((0 : A) : AlgebraicClosure ℚ)
        = (jBar N : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionFieldFull N)) (a : AlgebraicClosure ℚ) := by
      push_cast [hjel, hcel]
      simp [constantsHom]
    rw [h0]
    exact (w.mem_nonunits_iff_ord_pos hne).mpr ha
  have hnon : (fm.piFin (jel - cel) : modularFunctionFieldC k N)
      ∈ (fm.spPlace hred dataAll hsep w).toValuationSubring.nonunits := by
    rw [fm.piFin_mem_spPlace_nonunits_iff hred dataAll hsep w a ha (jel - cel)]
    exact ⟨0, Ideal.zero_mem _, hup⟩
  have hne2 : (fm.piFin (jel - cel) : modularFunctionFieldC k N) ≠ 0 := by
    rw [hπ]
    exact sub_ne_zero.mpr (ne_const_of_transcendental (transcendental_jC k N) (red a))
  have := ((fm.spPlace hred dataAll hsep w).mem_nonunits_iff_ord_pos hne2).mp hnon
  rwa [hπ] at this

end S_ModularCurve_CharPModel_FibreModel_spPlace_d0_j
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_j (solution)
