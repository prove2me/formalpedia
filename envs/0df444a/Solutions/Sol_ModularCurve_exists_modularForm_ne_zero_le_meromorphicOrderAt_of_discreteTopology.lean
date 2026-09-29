-- Prove2me | solution 1 for ModularCurve.exists_modularForm_ne_zero_le_meromorphicOrderAt_of_discreteTopology
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/c53cb3e3-5815-5190-9c3f-14fc95d6709a

import Mathlib
import Theorems.Thm_ModularCurve_exists_modularForm_separate_and_localParameter_of_discreteTopology
import Theorems.Thm_UpperHalfPlane_finite_stabilizer_and_isCyclic_of_det_eq_one
import Theorems.Thm_UpperHalfPlane_two_dvd_natCard_stabilizer_of_neg_one_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_modularForm_ne_zero_le_meromorphicOrderAt_of_discreteTopology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.longLine false

open scoped MatrixGroups Topology Manifold ModularForm
open UpperHalfPlane

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "exists_modularForm_separate_and_localParameter_of_discreteTopology"
namespace T3bAux
p2m_open "ModularCurve"

theorem analyticAt_comp_ofComplex {φ : ℍ → ℂ} (hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ) (τ : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => φ (ofComplex z)) (τ : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp hφ).analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

def mkForm (Γ : Subgroup (GL (Fin 2) ℝ)) (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ) (k : ℤ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hslash : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = denom γ τ ^ k * F τ) : ModularForm Γ k where
  toFun := F
  slash_action_eq' := by
    intro γ hγ
    funext τ
    have hd := hdet γ hγ
    rw [ModularForm.slash_def]
    dsimp only
    have hσ : σ γ (F (γ • τ)) = F (γ • τ) := by simp [σ, hd]
    rw [hσ, hslash γ hγ τ, hd]
    simp only [Units.val_one, abs_one, Complex.ofReal_one, one_zpow, mul_one]
    rw [zpow_neg, mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ (denom_ne_zero γ τ)), mul_comm]
  holo' := hF
  bdd_at_cusps' := fun hc => absurd hc (hcusp _)

@[scoped simp] theorem mkForm_apply (Γ : Subgroup (GL (Fin 2) ℝ)) (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ) (k : ℤ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hslash : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = denom γ τ ^ k * F τ) (τ : ℍ) :
    mkForm Γ hdet hcusp k F hF hslash τ = F τ := rfl

theorem pow_ne_zero_of_mdifferentiable {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (h0 : f ≠ 0) :
    ∀ n : ℕ, f ^ n ≠ 0 := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    intro h
    rcases (UpperHalfPlane.mul_eq_zero_iff (hf.pow m) hf).1 h with h' | h'
    · exact ih h'
    · exact h0 h'

theorem mdifferentiable_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ)
    (hf : ∀ i ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i)) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => (have h__af := (mdifferentiable_const : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun _ : ℍ => (1 : ℂ))); simp at h__af ⊢; exact h__af)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem zpow_mul_pow_eq (d g : ℂ) (k : ℤ) (m : ℕ) : (d ^ k * g) ^ m = d ^ ((m : ℤ) * k) * g ^ m := by
  rw [mul_pow, ← zpow_natCast (d ^ k) m, ← zpow_mul, mul_comm k]

end ModularCurve.T3bAux
p2m_reactivate "P2MW.S_ModularCurve_exists_modularForm_ne_zero_le_meromorphicOrderAt_of_discreteTopology.ModularCurve P2MW.S_ModularCurve_exists_modularForm_ne_zero_le_meromorphicOrderAt_of_discreteTopology.ModularCurve.T3bAux"
p2m_reactivate "P2MW.S_ModularCurve_exists_modularForm_ne_zero_le_meromorphicOrderAt_of_discreteTopology.ModularCurve"

open ModularCurve.T3bAux in
theorem solution
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    [hdisc : DiscreteTopology ↥Γ]
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ)
    (S : Finset ℍ) (n : ℍ → ℕ) :
    ∃ k : ℤ, 4 ≤ k ∧ Even k ∧ ∃ P : ModularForm Γ k, (P : ℍ → ℂ) ≠ 0 ∧
      ∀ τ ∈ S, ((n τ : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun z : ℂ => P (ofComplex z)) (τ : ℂ) := by
  classical

  haveI hΓ1 : Γ.HasDetOne := ⟨fun {γ} hγ => hdet γ hγ⟩
  haveI : Fact (Even (Fintype.card (Fin 2))) := ⟨by simp⟩
  set Γ' : Subgroup (GL (Fin 2) ℝ) := Γ.adjoinNegOne with hΓ'
  have hle : Γ ≤ Γ' := Γ.le_adjoinNegOne
  haveI : Γ'.HasDetOne := by rw [hΓ']; infer_instance
  have hdet' : ∀ γ ∈ Γ', Matrix.GeneralLinearGroup.det γ = 1 := fun γ hγ => Subgroup.HasDetOne.det_eq hγ
  have hneg' : -1 ∈ Γ' := Γ.negOne_mem_adjoinNegOne
  haveI : DiscreteTopology ↥Γ' := by rw [hΓ']; infer_instance
  have hcusp' : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ' := fun c hc =>
    hcusp c ((Γ.commensurable_adjoinNegOne_self).isCusp_iff.mp hc)

  have hb := (ModularCurve.exists_modularForm_separate_and_localParameter_of_discreteTopology
    Γ' hdet' hneg' hcusp').2
  choose kf hk4 hkev gf hf hh0 hord using hb

  have he : ∀ τ : ℍ, 1 ≤ Nat.card ↥(MulAction.stabilizer ↥Γ' τ) / 2 := by
    intro τ
    have hfin := (UpperHalfPlane.finite_stabilizer_and_isCyclic_of_det_eq_one Γ' hdet' τ).1
    have h2 := UpperHalfPlane.two_dvd_natCard_stabilizer_of_neg_one_mem Γ' hdet' hneg' τ
    haveI := hfin
    have hpos : 0 < Nat.card ↥(MulAction.stabilizer ↥Γ' τ) := Nat.card_pos
    omega

  have hgan : ∀ σ τ : ℍ, AnalyticAt ℂ (fun z : ℂ => gf σ (ofComplex z)) (τ : ℂ) :=
    fun σ τ => analyticAt_comp_ofComplex (gf σ).holo' τ
  have hhan : ∀ σ τ : ℍ, AnalyticAt ℂ (fun z : ℂ => hf σ (ofComplex z)) (τ : ℂ) :=
    fun σ τ => analyticAt_comp_ofComplex (hf σ).holo' τ

  have hordg : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => gf τ (ofComplex z)) (τ : ℂ) =
      (((Nat.card ↥(MulAction.stabilizer ↥Γ' τ) / 2 : ℕ) : ℤ) : WithTop ℤ) := by
    intro τ
    have hh : meromorphicOrderAt (fun z : ℂ => hf τ (ofComplex z)) (τ : ℂ) = 0 := by
      rw [(hhan τ τ).meromorphicOrderAt_eq, (hhan τ τ).analyticOrderAt_eq_zero.mpr]
      · simp
      · simpa only [ofComplex_apply] using hh0 τ
    have hev : (fun z : ℂ => gf τ (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
        ((fun z : ℂ => gf τ (ofComplex z)) / (fun z : ℂ => hf τ (ofComplex z))) *
          (fun z : ℂ => hf τ (ofComplex z)) := by
      have hne : ∀ᶠ z in 𝓝 (τ : ℂ), hf τ (ofComplex z) ≠ 0 :=
        (hhan τ τ).continuousAt.eventually_ne (by simpa only [ofComplex_apply] using hh0 τ)
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds hne] with z hz
      simp only [Pi.mul_apply, Pi.div_apply]
      rw [div_mul_cancel₀ _ hz]
    rw [meromorphicOrderAt_congr hev,
      meromorphicOrderAt_mul (((hgan τ τ).meromorphicAt).div (hhan τ τ).meromorphicAt) (hhan τ τ).meromorphicAt,
      hh, add_zero]
    exact hord τ
  have hg0 : ∀ τ : ℍ, (gf τ : ℍ → ℂ) ≠ 0 := by
    intro τ h0
    have : meromorphicOrderAt (fun z : ℂ => gf τ (ofComplex z)) (τ : ℂ) = ⊤ := by
      rw [meromorphicOrderAt_eq_top_iff]
      filter_upwards with z
      simp [h0]
    rw [hordg τ] at this
    exact WithTop.coe_ne_top this

  have hprod : ∀ γ ∈ Γ, ∀ (T : Finset ℍ) (z : ℍ),
      ∏ τ ∈ T, (gf τ (γ • z)) ^ (n τ) = denom γ z ^ (∑ τ ∈ T, (n τ : ℤ) * kf τ) * ∏ τ ∈ T, (gf τ z) ^ (n τ) := by
    intro γ hγ T z
    have hd : denom γ z ≠ 0 := denom_ne_zero γ z
    induction T using Finset.induction_on with
    | empty => simp
    | insert σ T hσ ih =>
      rw [Finset.prod_insert hσ, Finset.prod_insert hσ, Finset.sum_insert hσ, ih,
        SlashInvariantForm.slash_action_eqn'' (gf σ) (hle hγ) z, zpow_mul_pow_eq, zpow_add₀ hd]
      ring

  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = kf UpperHalfPlane.I + ∑ τ ∈ S, (n τ : ℤ) * kf τ := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℍ → ℂ, F = fun z => hf UpperHalfPlane.I z * ∏ τ ∈ S, (gf τ z) ^ (n τ) := ⟨_, rfl⟩
  have hF' : F = (hf UpperHalfPlane.I : ℍ → ℂ) * ∏ τ ∈ S, ((gf τ : ℍ → ℂ) ^ (n τ)) := by
    rw [hF]; funext z; simp [Finset.prod_apply]
  have hPmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (∏ τ ∈ S, ((gf τ : ℍ → ℂ) ^ (n τ))) :=
    mdifferentiable_finset_prod S _ fun τ _ => (gf τ).holo'.pow (n τ)
  have hFmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := by
    rw [hF']
    exact (hf UpperHalfPlane.I).holo'.mul hPmd
  have hslash : ∀ γ ∈ Γ, ∀ z : ℍ, F (γ • z) = denom γ z ^ K * F z := by
    intro γ hγ z
    rw [hF, hK]
    dsimp only
    rw [hprod γ hγ S z, SlashInvariantForm.slash_action_eqn'' (hf UpperHalfPlane.I) (hle hγ) z,
      zpow_add₀ (denom_ne_zero γ z)]
    ring
  let P : ModularForm Γ K := mkForm Γ hdet hcusp K F hFmd hslash
  have hP : (P : ℍ → ℂ) = F := rfl
  refine ⟨K, ?_, ?_, P, ?_, ?_⟩
  ·
    have : 0 ≤ ∑ τ ∈ S, (n τ : ℤ) * kf τ :=
      Finset.sum_nonneg fun τ _ => mul_nonneg (Int.natCast_nonneg _) (by linarith [hk4 τ])
    rw [hK]; linarith [hk4 UpperHalfPlane.I]
  ·
    rw [hK]
    refine (hkev UpperHalfPlane.I).add ?_
    rw [even_iff_two_dvd]
    exact Finset.dvd_sum fun τ _ => (even_iff_two_dvd.mp (hkev τ)).mul_left _
  ·
    rw [hP, hF']
    intro h0
    rcases (UpperHalfPlane.mul_eq_zero_iff (hf UpperHalfPlane.I).holo' hPmd).1 h0 with h | h
    · exact hh0 UpperHalfPlane.I (by simpa using congrFun h UpperHalfPlane.I)
    · obtain ⟨σ, hσ, hσ0⟩ :=
        (UpperHalfPlane.prod_eq_zero_iff fun τ _ => (gf τ).holo'.pow (n τ)).1 h
      exact pow_ne_zero_of_mdifferentiable (gf σ).holo' (hg0 σ) (n σ) hσ0
  ·
    intro τ hτS
    rw [hP]
    have hfun : (fun z : ℂ => F (ofComplex z)) =
        (fun z : ℂ => hf UpperHalfPlane.I (ofComplex z)) *
          ∏ σ ∈ S, (fun z : ℂ => gf σ (ofComplex z)) ^ (n σ) := by
      rw [hF]; funext z; simp [Finset.prod_apply]
    rw [hfun, meromorphicOrderAt_mul (hhan UpperHalfPlane.I τ).meromorphicAt
        (MeromorphicAt.prod fun σ _ => ((hgan σ τ).meromorphicAt).pow (n σ)),
      meromorphicOrderAt_prod fun σ _ => ((hgan σ τ).meromorphicAt).pow (n σ)]
    have hterm : ∀ σ ∈ S, 0 ≤ meromorphicOrderAt ((fun z : ℂ => gf σ (ofComplex z)) ^ (n σ)) (τ : ℂ) :=
      fun σ _ => ((hgan σ τ).pow (n σ)).meromorphicOrderAt_nonneg
    have hτterm : ((n τ : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt ((fun z : ℂ => gf τ (ofComplex z)) ^ (n τ)) (τ : ℂ) := by
      rw [meromorphicOrderAt_pow (hgan τ τ).meromorphicAt, hordg τ]
      have h1 := he τ
      have h2 : (n τ : ℤ) ≤ (n τ : ℤ) * ((Nat.card ↥(MulAction.stabilizer ↥Γ' τ) / 2 : ℕ) : ℤ) := by
        have : (1 : ℤ) ≤ ((Nat.card ↥(MulAction.stabilizer ↥Γ' τ) / 2 : ℕ) : ℤ) := by exact_mod_cast h1
        nlinarith
      exact_mod_cast h2
    calc ((n τ : ℤ) : WithTop ℤ)
        ≤ meromorphicOrderAt ((fun z : ℂ => gf τ (ofComplex z)) ^ (n τ)) (τ : ℂ) := hτterm
      _ ≤ ∑ σ ∈ S, meromorphicOrderAt ((fun z : ℂ => gf σ (ofComplex z)) ^ (n σ)) (τ : ℂ) :=
          Finset.single_le_sum hterm hτS
      _ ≤ _ := le_add_of_nonneg_left (hhan UpperHalfPlane.I τ).meromorphicOrderAt_nonneg

end
end S_ModularCurve_exists_modularForm_ne_zero_le_meromorphicOrderAt_of_discreteTopology
end P2MW
export P2MW.S_ModularCurve_exists_modularForm_ne_zero_le_meromorphicOrderAt_of_discreteTopology (solution)
