-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan.snd_eq_zero_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:37:08.033372+00:00
-- url     : https://prove2.me/submissions/d25fe15f-29ef-43f8-a011-94e3da7db489

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsAlgHomAdjoinInv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SndEqZeroOfSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan
open TrivSqZeroExt
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan
theorem _root_.solution {S : Type} [CommRing S] [Algebra ℚ S]
    (φ : S →ₐ[ℚ] TrivSqZeroExt ℂ ℂ) {e : ℕ} (z : Fin e → S)
    (hspan : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤)
    (h : ∀ i, snd (φ (z i)) = 0) (s : S) : snd (φ s) = 0 := by
  let f : S →+* ℂ := (TrivSqZeroExt.fstHom ℚ ℂ ℂ).toRingHom.comp φ.toRingHom
  letI : Module S ℂ := Module.compHom ℂ f
  haveI : IsScalarTower ℚ S ℂ := ⟨fun q a m => by
    show f (q • a) * m = q • (f a * m)
    rw [Algebra.smul_def, map_mul, Algebra.smul_def, mul_assoc]
    congr 1
    exact (eq_ratCast (f.comp (algebraMap ℚ S)) q).trans (eq_ratCast (algebraMap ℚ ℂ) q).symm⟩
  let d : Derivation ℚ S ℂ :=
    { toFun := fun a => snd (φ a)
      map_add' := fun a b => by simp
      map_smul' := fun q a => by simp
      map_one_eq_zero' := by simp
      leibniz' := fun a b => by
        show snd (φ (a * b)) = (φ a).fst * snd (φ b) + (φ b).fst * snd (φ a)
        rw [map_mul, snd_mul, smul_eq_mul, op_smul_eq_mul]
        ring }
  have key : d.liftKaehlerDifferential = 0 := by
    refine LinearMap.ext_on_range hspan fun i => ?_
    rw [Derivation.liftKaehlerDifferential_comp_D]
    exact h i
  have h2 := congrArg (fun L => L (KaehlerDifferential.D ℚ S s)) key
  simpa [Derivation.liftKaehlerDifferential_comp_D, d] using h2
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan
