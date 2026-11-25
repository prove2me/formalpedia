-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.exists_frobenius_semisimplification
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:13:17.458127+00:00
-- url     : https://prove2.me/submissions/6b24586c-e886-45d6-ba1f-9832f9e82356

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPowEqPowOfWeilDegreeEqSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeilGroupIsSemisimpleOfSemisimpleFrobStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFrobeniusSemisimplification
import Theorems.Thm_GlobalTheory_WeilDeligne_semisimplePart_mul_eq
import Theorems.Thm_GlobalTheory_WeilDeligne_isNilpotent_pow_sub_one
import Theorems.Thm_GlobalTheory_WeilDeligne_commute_of_commute_pow
import Theorems.Thm_GlobalTheory_T_exists_pow_eq_pow_of_weilDegree_eq_smooth
import Theorems.Thm_GlobalTheory_T_weilGroup_isSemisimple_of_semisimple_frob
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_lpSp
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDual_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpChar_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_lpSp
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDual_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpSum_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.unr_mk
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne
namespace GlobalTheory.WeilDeligne
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ (Weil h) V) (N : End ℂ V), IsSmooth ρ → IsNilpotent N → (∀ σ, ρ σ * N = ((normV w : ℕ) : ℂ) ^ deg σ • (N * ρ σ)) → ∃ (a : WDRep h V) (u : (End ℂ V)ˣ), a.N = N ∧ IsNilpotent ((u : End ℂ V) - 1) ∧ Commute (u : End ℂ V) N ∧ (∀ σ, Commute (u : End ℂ V) (ρ σ)) ∧ ∀ σ, ρ σ = a.ρ σ * ((u ^ deg σ : (End ℂ V)ˣ) : End ℂ V) := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ ρ N hρ hN hc
  obtain ⟨n, hn, s, hs, hnil, hss, hf⟩ := End.exists_isNilpotent_isSemisimple (f := ρ (frob h))
  set f := ρ (frob h) with hfdef
  have hfn : Commute f n := Algebra.commute_of_mem_adjoin_self hn
  have hfs : Commute f s := Algebra.commute_of_mem_adjoin_self hs
  have hsub : f - s = n := by rw [hf]; simp
  have hns : Commute n s := by rw [← hsub]; exact hfs.sub_left (Commute.refl s)
  have hfu : IsUnit f := (Group.isUnit (frob h)).map ρ
  have hsu : IsUnit s := by
    have : s = f + -n := by rw [← hsub]; simp
    rw [this]
    exact hnil.neg.isUnit_add_left_of_commute hfu hfn.symm.neg_left
  obtain ⟨S, rfl⟩ := hsu
  obtain ⟨F, hF⟩ := hfu
  have hFS : Commute F S := by
    exact Units.ext (by rw [Units.val_mul, Units.val_mul, hF]; exact hfs.eq)
  set u : (End ℂ V)ˣ := S⁻¹ * F with hu
  have huS : Commute u S := (Commute.refl S).inv_left.mul_left hFS
  have hSu : S * u = F := by simp [hu]
  have hSu' : (S : End ℂ V) * u = f := by rw [← Units.val_mul, hSu, hF]
  have huS' : Commute (u : End ℂ V) (S : End ℂ V) := huS.units_val
  have hunil : IsNilpotent ((u : End ℂ V) - 1) := by
    have : (u : End ℂ V) - 1 = n * (S⁻¹ : (End ℂ V)ˣ) := by
      rw [hns.units_inv_right.eq, ← hsub, hu, Units.val_mul, hF, mul_sub]; simp
    rw [this]
    exact hns.units_inv_right.isNilpotent_mul_right hnil
  have huN : Commute (u : End ℂ V) N := by
    have h1 := hc (frob h)
    have h2 := semisimplePart_mul_eq hfs hss (hsub ▸ hnil) h1
    have hq : ((normV w : ℕ) : ℂ) ^ deg (frob h) ≠ 0 :=
      zpow_ne_zero _ (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot)
    have h3 : (S : End ℂ V) * ((u : End ℂ V) * N) = S * (N * u) := by
      rw [← mul_assoc, hSu', h1, ← mul_assoc, h2, smul_mul_assoc, mul_assoc, hSu']
    exact (Units.mul_right_inj S).mp h3
  have huρ : ∀ τ, Commute (u : End ℂ V) (ρ τ) := by
    intro τ
    obtain ⟨m, hm, e⟩ := GlobalTheory.T.exists_pow_eq_pow_of_weilDegree_eq_smooth E Ω A w h V ρ hρ (frob h) (τ * frob h * τ⁻¹) (by simp)
    have c1 : f ^ m * ρ τ = (1 : ℂ) • (ρ τ * f ^ m) := by
      rw [one_smul]
      conv_lhs => rw [hfdef, e]
      rw [hfdef, ← map_pow, ← map_pow, ← map_mul, ← map_mul, conj_pow]
      simp
    have epow : f ^ m = (S : End ℂ V) ^ m * (u : End ℂ V) ^ m := by
      rw [← huS'.symm.mul_pow, hSu']
    have c2 := semisimplePart_mul_eq (hfs.pow_pow m m) (hss.pow m) (by
      have : f ^ m - (S : End ℂ V) ^ m = ((u : End ℂ V) ^ m - 1) * (S : End ℂ V) ^ m := by
        rw [epow, sub_mul, (huS'.pow_pow m m).eq, one_mul]
      rw [this]
      exact ((huS'.pow_pow m m).sub_left (Commute.one_left _)).isNilpotent_mul_right
        (isNilpotent_pow_sub_one hunil m)) c1
    rw [one_smul] at c1 c2
    refine commute_of_commute_pow hm hunil ?_
    have h3 : ((S ^ m : (End ℂ V)ˣ) : End ℂ V) * ((u : End ℂ V) ^ m * ρ τ) =
        (S ^ m : (End ℂ V)ˣ) * (ρ τ * (u : End ℂ V) ^ m) := by
      rw [Units.val_pow_eq_pow_val, ← mul_assoc, ← epow, c1, ← mul_assoc, c2, mul_assoc, ← epow]
    exact (Units.mul_right_inj _).mp h3
  let ρ' : Representation ℂ (Weil h) V :=
    { toFun := fun σ => ρ σ * ((u ^ (-deg σ) : (End ℂ V)ˣ) : End ℂ V)
      map_one' := by simp
      map_mul' := fun σ τ => by
        have := ((huρ τ).units_zpow_left (-deg σ)).eq
        rw [map_mul, deg_mul, neg_add, zpow_add, Units.val_mul]
        simp only [mul_assoc]
        rw [← mul_assoc _ (ρ τ) (Units.val (u ^ (-deg τ))), this, mul_assoc] }
  have hρ' : ∀ σ, ρ' σ = ρ σ * ((u ^ (-deg σ) : (End ℂ V)ˣ) : End ℂ V) := fun _ => rfl
  have hsm : IsSmooth ρ' := .of_open hρ (by simp) fun σ hσ => by
    have : ρ (ineIncl h σ) = 1 := hσ
    rw [hρ', this]; simp
  have hfr : ρ' (frob h) = S := by
    rw [hρ', deg_frob, ← hfdef, ← hSu', mul_assoc, ← Units.val_mul]; simp
  refine ⟨⟨ρ', N, hsm, GlobalTheory.T.weilGroup_isSemisimple_of_semisimple_frob E Ω A w h V ρ' hsm (frob h) deg_frob (hfr ▸ hss), hN,
    fun σ => ?_⟩, u, rfl, hunil, huN, huρ, fun σ => ?_⟩
  · rw [hρ', mul_assoc, (huN.units_zpow_left (-deg σ)).eq, ← mul_assoc, hc, smul_mul_assoc,
      mul_assoc]
  · show _ = ρ' σ * _
    rw [hρ', mul_assoc, ← Units.val_mul, ← zpow_add]; simp
end GlobalTheory.WeilDeligne
