-- Prove2me | solution 1 for GlobalTheory.QNorm.sUnits_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:58:53.053608+00:00
-- url     : https://prove2.me/submissions/3a60c7cd-5f87-4f51-9b1a-7a48b9999c53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsNumberFieldFg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FinrankSUnitsNumberFieldAddOne
import Theorems.Thm_GlobalTheory_QNorm_exists_mem_only
import Theorems.Thm_GlobalTheory_QNorm_mem_sUnits
import Theorems.Thm_GlobalTheory_QNorm_sUnits_fg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
noncomputable section
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
      Module.finrank ℤ (Additive (sUnits F S)) + 1 = S.card + Fintype.card (InfinitePlace F) := by
  intro F _ _ S
  classical
  have hunit : ∀ (u : (𝓞 F)ˣ) (v : HeightOneSpectrum (𝓞 F)),
      v.valuation F (algebraMap (𝓞 F) F u) = 1 := by
    intro u v
    rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
    intro hu
    exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hu u.isUnit)
  let f0 : (𝓞 F)ˣ →* sUnits F S :=
    (Units.map (algebraMap (𝓞 F) F).toMonoidHom).codRestrict _
      (fun u => (mem_sUnits F S _).2 fun v _ => hunit u v)
  let f : Additive (𝓞 F)ˣ →ₗ[ℤ] Additive (sUnits F S) :=
    (MonoidHom.toAdditive f0).toIntLinearMap
  let g0 : Additive (sUnits F S) →+ (S → ℤ) :=
    AddMonoidHom.mk' (fun x v => WithZero.log
      ((v : HeightOneSpectrum (𝓞 F)).valuation F (((Additive.toMul x : sUnits F S) : Fˣ) : F))) (by
      intro a b
      funext v
      simp only [toMul_add, Subgroup.coe_mul, Units.val_mul, map_mul, Pi.add_apply]
      exact WithZero.log_mul (by simp) (by simp))
  let g := g0.toIntLinearMap
  have hker : LinearMap.ker g = LinearMap.range f := by
    apply le_antisymm
    · intro x hx
      set y : Fˣ := ((Additive.toMul x : sUnits F S) : Fˣ) with hy
      have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (y : F) = 1 := by
        intro v
        by_cases hv : v ∈ S
        · have h : WithZero.log (v.valuation F (y : F)) = 0 :=
            congrFun (LinearMap.mem_ker.1 hx) ⟨v, hv⟩
          have hne : v.valuation F (y : F) ≠ 0 := by simp
          rw [← WithZero.exp_log hne, h, WithZero.exp_zero]
        · exact (mem_sUnits F S _).1 (Additive.toMul x).2 v hv
      obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y : F)
        (fun v => (hall v).le)
      obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y : F)⁻¹
        (fun v => by rw [map_inv₀, hall v, inv_one])
      have hab : a * b = 1 := by
        apply IsFractionRing.injective (𝓞 F) F
        rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ y.ne_zero]
      refine ⟨Additive.ofMul (Units.mkOfMulEqOne a b hab), ?_⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      exact ha
    · rintro _ ⟨u, rfl⟩
      rw [LinearMap.mem_ker]
      funext v
      change WithZero.log ((v : HeightOneSpectrum (𝓞 F)).valuation F
        (algebraMap (𝓞 F) F (Additive.toMul u : (𝓞 F)ˣ))) = 0
      rw [hunit, WithZero.log_one]
  have hinj : Function.Injective f := by
    intro a b hab
    apply Additive.toMul.injective
    apply Units.ext
    apply IsFractionRing.injective (𝓞 F) F
    exact congrArg (fun x : Additive (sUnits F S) => (((Additive.toMul x : sUnits F S) : Fˣ) : F)) hab
  have hfin : Module.Finite ℤ (Additive (sUnits F S)) :=
    Module.Finite.iff_addGroup_fg.2 (GroupFG.iff_add_fg.1 (sUnits_fg F S))
  have hrange : Module.finrank ℤ (LinearMap.range g) = S.card := by
    apply le_antisymm
    · refine (Submodule.finrank_le _).trans ?_
      simp
    · have key : ∀ v : S, ∃ c : ℤ, c ≠ 0 ∧ Pi.single v c ∈ LinearMap.range g := by
        intro v
        obtain ⟨a, ha0, hav, haw⟩ := exists_mem_only F v
        have ha0' : algebraMap (𝓞 F) F a ≠ 0 := by simpa using ha0
        have hw : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
            w.valuation F (algebraMap (𝓞 F) F a) = 1 := fun w hw =>
          (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 (haw w hw)
        refine ⟨WithZero.log ((v : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a)),
          ?_, Additive.ofMul ⟨Units.mk0 _ ha0', (mem_sUnits F S _).2 fun w hwS =>
            hw w (fun e => hwS (e ▸ v.2))⟩, ?_⟩
        · intro h0
          have hne : (v : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a) ≠ 0 := by
            simpa using ha0
          have h1 : (v : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a) = 1 := by
            rw [← WithZero.exp_log hne, h0, WithZero.exp_zero]
          exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).1 h1 hav
        · funext w
          change WithZero.log ((w : HeightOneSpectrum (𝓞 F)).valuation F
            (algebraMap (𝓞 F) F a)) = _
          by_cases hwv : w = v
          · subst hwv; simp
          · rw [Pi.single_eq_of_ne hwv, hw w (fun e => hwv (Subtype.ext e)), WithZero.log_one]
      choose c hc0 hc using key
      have hli : LinearIndependent ℤ (fun v : S => (⟨Pi.single v (c v), hc v⟩ : LinearMap.range g)) :=
        LinearIndependent.of_comp (LinearMap.range g).subtype
          (Pi.linearIndependent_single_of_ne_zero hc0)
      simpa using hli.fintype_card_le_finrank
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker g)
  rw [g.quotKerEquivRange.finrank_eq, hrange, hker, LinearMap.finrank_range_of_inj hinj,
    NumberField.Units.finrank_eq, NumberField.Units.rank] at h1
  have h2 : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  omega
end GlobalTheory.QNorm
