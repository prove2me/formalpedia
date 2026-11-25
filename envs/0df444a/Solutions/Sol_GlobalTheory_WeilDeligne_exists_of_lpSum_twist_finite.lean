-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.exists_of_lpSum_twist_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:12:38.244268+00:00
-- url     : https://prove2.me/submissions/699af5f7-b101-4c59-aef0-31a66b56cc4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_Mono0OfLpDimEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAevalEqSmulOnEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilDeligneInductionPrinciple
import Theorems.Thm_GlobalTheory_WeilDeligne_WDRep_charpoly_eq_mul_of_isCompl
import Theorems.Thm_GlobalTheory_WeilDeligne_finite_range_of_frob_pow_eq_one
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_charPol_lpSum
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_lpSp
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDual_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_exists_pow_frob_commute
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
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
namespace GlobalTheory.WeilDeligne
theorem _root_.solution (S : WD h → Prop)
    (hsum : ∀ x y, S x → S y → S (x.lpSum y))
    (hfin : ∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ),
      (Set.range a.ρ).Finite → S (WD.mk (a.twist μ hμ))) :
    ∀ (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
      finrank ℂ V = d → ∀ (ρ : Representation ℂ (Weil h) V), IsSmooth ρ →
      (∀ σ, End.IsSemisimple (ρ σ)) → ∃ y : WD h, S y ∧ ∀ σ, y.charPol σ = (ρ σ).charpoly := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V _ _ _ hd ρ hρ hs
  let a0 : WDRep h V := ⟨ρ, 0, hρ, hs, IsNilpotent.zero, by simp⟩
  obtain ⟨m, hm, hcomm⟩ := exists_pow_frob_commute ρ hρ
  have hsm : ρ (frob h) ^ m = ρ (frob h ^ m) := (map_pow _ _ _).symm
  by_cases hsc : ∃ c : ℂ, c ≠ 0 ∧ ρ (frob h) ^ m = c • (1 : Module.End ℂ V)
  · obtain ⟨c, hc0, hsc⟩ := hsc
    obtain ⟨c', hc'⟩ := IsAlgClosed.exists_pow_nat_eq c hm
    have hc'0 : c' ≠ 0 := by rintro rfl; exact hc0 (by rw [← hc', zero_pow hm.ne'])
    set u : ℂˣ := Units.mk0 c' hc'0
    let b : WDRep h V := a0.twist (unrChar h u⁻¹) (isSmooth_unrChar h _)
    have hb1 : b.ρ (frob h) ^ m = 1 := by
      show ((((unrChar h u⁻¹) (frob h) : ℂˣ) : ℂ) • ρ (frob h)) ^ m = 1
      rw [_root_.smul_pow, hsc, smul_smul, unrChar_apply, deg_frob, zpow_one, ← Units.val_pow_eq_pow_val,
        inv_pow]
      have : u ^ m = Units.mk0 c hc0 := Units.ext (by simp [u, hc'])
      rw [this]
      simp [hc0]
    have hfinb := finite_range_of_frob_pow_eq_one b.ρ b.smooth hm hb1
    have hfins : (Set.range (WD.std b).2.ρ).Finite :=
      (hfinb.image ((finBasis ℂ V).equivFun.conjAlgEquiv ℂ)).subset (by rintro _ ⟨σ, rfl⟩; exact ⟨_, ⟨σ, rfl⟩, rfl⟩)
    refine ⟨WD.mk ((WD.std b).2.twist (unrChar h u) (isSmooth_unrChar h _)),
      hfin _ _ _ _ hfins, fun σ => ?_⟩
    rw [← WD.sound ((WD.iso_std b).twist _ _), WD.charPol_mk]
    show ((((unrChar h u) σ : ℂˣ) : ℂ) • ((((unrChar h u⁻¹) σ : ℂˣ) : ℂ) • ρ σ)).charpoly = _
    rw [smul_smul, ← Units.val_mul, unrChar_apply, unrChar_apply, ← mul_zpow, mul_inv_cancel,
      one_zpow, Units.val_one, one_smul]
  · have hnt : Nontrivial V := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      exact hsc ⟨1, one_ne_zero, LinearMap.ext fun v => Subsingleton.elim _ _⟩
    set s := ρ (frob h) ^ m with hs_def
    have hss : End.IsSemisimple s := by rw [hsm]; exact hs _
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue s
    have hinv : ∀ σ α, ∀ v ∈ End.eigenspace s α, ρ σ v ∈ End.eigenspace s α := by
      intro σ α v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [← Module.End.mul_apply, (hcomm σ).eq, Module.End.mul_apply, hv, map_smul]
    set U := End.eigenspace s c
    set U' := ⨆ α ∈ ({c}ᶜ : Set ℂ), End.eigenspace s α
    have hU : ∀ σ, ∀ v ∈ U, ρ σ v ∈ U := fun σ => hinv σ c
    have hU' : ∀ σ, ∀ v ∈ U', ρ σ v ∈ U' := by
      intro σ v hv
      have : U' ≤ U'.comap (ρ σ) := iSup₂_le fun α hα w hw =>
        (le_iSup₂_of_le α hα le_rfl : End.eigenspace s α ≤ U') (hinv σ α w hw)
      exact this hv
    have hcompl : IsCompl U U' := by
      refine ⟨(Module.End.eigenspaces_iSupIndep s).disjoint_biSup (by simp), ?_⟩
      rw [codisjoint_iff, eq_top_iff, ← hss.iSup_eigenspace_eq_top]
      refine iSup_le fun α => ?_
      by_cases hα : α = c
      · subst hα; exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂_of_le α hα le_rfl)
    have hc0 : c ≠ 0 := by
      rintro rfl
      obtain ⟨v, hv, hv0⟩ := hc.exists_hasEigenvector
      apply hv0
      have h1 := Module.End.mem_eigenspace_iff.mp hv
      rw [zero_smul] at h1
      have h1' : ρ (frob h ^ m) v = 0 := by rw [← hsm]; exact h1
      have := congrArg (ρ (frob h ^ m)⁻¹) h1'
      rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
        map_zero] at this
    have hUb : U ≠ ⊥ := hc
    have hU'b : U' ≠ ⊥ := by
      intro hb
      apply hsc
      refine ⟨c, hc0, LinearMap.ext fun v => ?_⟩
      have hv : v ∈ U := by
        have := hcompl.sup_eq_top
        rw [hb, sup_bot_eq] at this
        rw [this]; trivial
      rw [Module.End.mem_eigenspace_iff.mp hv]
      simp
    have hrk := Submodule.finrank_add_eq_of_isCompl hcompl
    have h1 : 0 < finrank ℂ U := Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hUb)
    have h2 : 0 < finrank ℂ U' :=
      Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hU'b)
    obtain ⟨y1, hS1, hy1⟩ := ih (finrank ℂ U) (by omega) U rfl (a0.resZero U hU).ρ
      (a0.resZero U hU).smooth (a0.resZero U hU).semisimple
    obtain ⟨y2, hS2, hy2⟩ := ih (finrank ℂ U') (by omega) U' rfl (a0.resZero U' hU').ρ
      (a0.resZero U' hU').smooth (a0.resZero U' hU').semisimple
    refine ⟨y1.lpSum y2, hsum _ _ hS1 hS2, fun σ => ?_⟩
    rw [WD.charPol_lpSum, hy1, hy2]
    exact (a0.charpoly_eq_mul_of_isCompl U U' hU hU' hcompl σ).symm
end GlobalTheory.WeilDeligne
