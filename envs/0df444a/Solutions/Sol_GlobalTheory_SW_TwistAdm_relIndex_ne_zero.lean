-- Prove2me | solution 1 for GlobalTheory.SW.TwistAdm.relIndex_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:35.63545+00:00
-- url     : https://prove2.me/submissions/f95de3fd-4291-4631-8f19-ac12be904352

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistAdm
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
namespace GlobalTheory.SW.TwistAdm
namespace _root_.GlobalTheory.SW.TwistAdm
theorem _root_.solution (A B : _root_.GlobalTheory.SW.Lt E N)
    (hB : B.FG) {t : ℕ} (ht : 0 < t)
    (h : ∀ v ∈ B, (t : E) • v ∈ A) : A.toAddSubgroup.relIndex B.toAddSubgroup ≠ 0 := by
  set I : Ideal (𝓞 E) := Ideal.span {(t : 𝓞 E)} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast ht.ne'
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  haveI : Finite (B ⧸ (⊤ : Submodule (𝓞 E) B)) := inferInstance
  have hfin : Finite (B ⧸ I • (⊤ : Submodule (𝓞 E) B)) :=
    Submodule.finite_quotient_smul I ((Submodule.fg_top B).mpr hB)
  have hle : I • (⊤ : Submodule (𝓞 E) B) ≤ A.comap B.subtype := by
    rw [Submodule.smul_le]
    intro r hr b _
    obtain ⟨r', rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have key : ((t : 𝓞 E)) • (b : Fin N → E) = (t : E) • (b : Fin N → E) := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul, mul_smul, key]
    exact A.smul_mem r' (h b b.2)
  haveI : Finite (B ⧸ A.comap B.subtype) :=
    Finite.of_surjective (Submodule.factor hle) (by
      rintro ⟨x⟩
      exact ⟨Submodule.Quotient.mk x, rfl⟩)
  exact @AddSubgroup.index_ne_zero_of_finite _ _ _ this
end _root_.GlobalTheory.SW.TwistAdm
end GlobalTheory.SW.TwistAdm
