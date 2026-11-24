-- Prove2me | solution 1 for GlobalTheory.UnramSelfDual.exists_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:39:13.791598+00:00
-- url     : https://prove2.me/submissions/30aefa0f-8379-4b61-896e-e11f905bfbe6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsSubConjNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsReflection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SelfDualLatticeProjectionMemOfUnitLength
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsOfFixedInt
import Theorems.Thm_GlobalTheory_UnramSelfDual_sigR_algebraMap
import Theorems.Thm_GlobalTheory_UnramSelfDual_exists_of_fixed_int
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SelfDualLatticeActions_sigR_mem
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryLatticeOrthogonal_sigR_mem
import Theorems.Thm_GlobalTheory_SelfDualGenus_finite_residueField_adicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_isAdicComplete_adicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_sigR_sigR


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal Formalism.UG
open GlobalTheory GlobalTheory.UnramSelfDual
open GlobalTheory.SelfDualLatticeCompare IsLocalRing
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (v : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.UnramSelfDual
theorem _root_.solution (h : IsCMExt F E σ)
    (hθ : ∃ θ ∈ OEv F E v, ∃ b ∈ OEv F E v, (θ - sigR (Fv F v) σ θ) * b = 1) :
    ∀ a ∈ OEv F E v, sigR (Fv F v) σ a = a → (∃ b ∈ OEv F E v, a * b = 1) →
      ∃ x ∈ OEv F E v, sigR (Fv F v) σ x * x = a := by
  rintro a ha hc ⟨b, hb, hab⟩
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  let c : OEv F E v →+* OEv F E v :=
    (sigR (Fv F v) σ).restrict (OEv F E v).toSubring (OEv F E v).toSubring fun _ => sigR_mem σ v
  obtain ⟨θ, hθO, t, ht, hθt⟩ := hθ
  obtain ⟨x, hx⟩ := GlobalTheory.UnramifiedHermitian.exists_norm_eq_of_henselian
    (R₀ := v.adicCompletionIntegers F) c (fun x => Subtype.ext (sigR_sigR (Fv F v) h (x : Ev F E v)))
    (fun r => Subtype.ext (sigR_algebraMap v (r : Fv F v)))
    (fun x hx => by
      obtain ⟨r, hr⟩ := exists_of_fixed_int v h x.2 (congrArg Subtype.val hx)
      exact ⟨r, Subtype.ext hr⟩)
    ⟨⟨θ, hθO⟩, IsUnit.of_mul_eq_one ⟨t, ht⟩ (Subtype.ext hθt)⟩
    (u := ⟨a, ha⟩) (Subtype.ext hc) (IsUnit.of_mul_eq_one ⟨b, hb⟩ (Subtype.ext hab))
  exact ⟨x, x.2, by rw [mul_comm]; exact congrArg Subtype.val hx⟩
end GlobalTheory.UnramSelfDual
