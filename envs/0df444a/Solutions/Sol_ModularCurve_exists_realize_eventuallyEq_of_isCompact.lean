-- Prove2me | solution 1 for ModularCurve.exists_realize_eventuallyEq_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/8e19b88d-a2d6-5bec-ab46-6a40ea274467

import Mathlib
import Definitions.Def_ModularCurve_AutomorphicField
import Theorems.Thm_ModularCurve_automorphicField_realize_laws
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_realize_eventuallyEq_of_isCompact

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.longLine false

open scoped MatrixGroups Topology Manifold ModularForm
open UpperHalfPlane

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "holRing merRealize automorphicField automorphicField.realize automorphicField_realize_laws"
namespace T7Aux
p2m_open "ModularCurve"

theorem map_coe_nhdsNE (τ : ℍ) :
    Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] τ) = 𝓝[≠] (τ : ℂ) := by
  have h := UpperHalfPlane.isOpenEmbedding_coe.map_nhdsWithin_preimage_eq {(τ : ℂ)}ᶜ τ
  have : ((↑) : ℍ → ℂ) ⁻¹' {(τ : ℂ)}ᶜ = {τ}ᶜ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, UpperHalfPlane.ext_iff]
  rw [this] at h
  exact h

scoped instance nhdsNE_neBot (τ : ℍ) : (𝓝[≠] τ).NeBot := by
  have : (Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] τ)).NeBot := by
    rw [map_coe_nhdsNE]; infer_instance
  exact Filter.NeBot.of_map this

theorem eventually_coe_iff {τ : ℍ} {p : ℂ → Prop} :
    (∀ᶠ (w : ℍ) in 𝓝[≠] τ, p (UpperHalfPlane.coe w)) ↔ ∀ᶠ z in 𝓝[≠] (τ : ℂ), p z := by
  rw [← map_coe_nhdsNE, Filter.eventually_map]

theorem eventually_ofComplex_iff {τ : ℍ} {p : ℍ → Prop} :
    (∀ᶠ z in 𝓝[≠] (τ : ℂ), p (ofComplex z)) ↔ ∀ᶠ z in 𝓝[≠] τ, p z := by
  rw [← map_coe_nhdsNE, Filter.eventually_map]
  simp only [ofComplex_apply]

theorem tendsto_smul_nhdsNE (g : GL (Fin 2) ℝ) (τ : ℍ) :
    Filter.Tendsto (fun z : ℍ => g • z) (𝓝[≠] τ) (𝓝[≠] (g • τ)) := by
  refine ((continuous_const_smul g).continuousWithinAt).tendsto_nhdsWithin ?_
  intro z hz h
  exact hz (MulAction.injective g h)

theorem analyticAt_comp_ofComplex {φ : ℍ → ℂ} (hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ) (τ : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => φ (ofComplex z)) (τ : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp hφ).analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

theorem det_pos_of_mem {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γ) :
    0 < γ.val.det := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, Subgroup.HasDetOne.det_eq hγ, Units.val_one]
  exact one_pos

end ModularCurve.T7Aux
p2m_reactivate "P2MW.S_ModularCurve_exists_realize_eventuallyEq_of_isCompact.ModularCurve P2MW.S_ModularCurve_exists_realize_eventuallyEq_of_isCompact.ModularCurve.T7Aux"
p2m_reactivate "P2MW.S_ModularCurve_exists_realize_eventuallyEq_of_isCompact.ModularCurve"

open ModularCurve.T7Aux in
theorem solution
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    [hdisc : DiscreteTopology ↥Γ]
    (hcpt : ∃ K : Set ℍ, IsCompact K ∧ ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ K)
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ)
    (hample : ∀ (S : Finset ℍ) (n : ℍ → ℕ),
      ∃ k : ℤ, 4 ≤ k ∧ Even k ∧ ∃ P : ModularForm Γ k, (P : ℍ → ℂ) ≠ 0 ∧
        ∀ τ ∈ S, ((n τ : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun z : ℂ => P (ofComplex z)) (τ : ℂ))
    (f : ℍ → ℂ) (hf : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => f (ofComplex z)) (τ : ℂ))
    (hinv : ∀ γ ∈ Γ, ∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ, f (γ • z) = f z) :
    ∃ x : ↥(ModularCurve.automorphicField Γ),
      ∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ, ModularCurve.automorphicField.realize x z = f z := by
  classical
  obtain ⟨K, hK, hKcov⟩ := hcpt
  have hPholo : ∀ {k : ℤ} (Q : ModularForm Γ k), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Q : ℍ → ℂ) :=
    fun Q => Q.holo'

  have hiso : ∀ τ : ℍ, ∀ᶠ (w : ℍ) in 𝓝[≠] τ,
      ¬ meromorphicOrderAt (fun z : ℂ => f (ofComplex z)) (UpperHalfPlane.coe w) < 0 := by
    intro τ
    have hev := (hf τ).eventually_analyticAt
    refine (eventually_coe_iff.mpr hev).mono fun z hz => ?_
    exact not_lt.mpr hz.meromorphicOrderAt_nonneg
  have hfinK : {τ : ℍ | τ ∈ K ∧ meromorphicOrderAt (fun z : ℂ => f (ofComplex z)) (τ : ℂ) < 0}.Finite := by
    obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover
      (fun τ => {z : ℍ | z ∈ ({τ}ᶜ : Set ℍ) →
        ¬ meromorphicOrderAt (fun z : ℂ => f (ofComplex z)) (z : ℂ) < 0})
      (fun τ _ => eventually_nhdsWithin_iff.mp (hiso τ))
    refine t.finite_toSet.subset ?_
    rintro z ⟨hzK, hzord⟩
    obtain ⟨τ, hτt, hzU⟩ := Set.mem_iUnion₂.mp (hcov hzK)
    have hzτ : z = τ := by
      by_contra hne
      exact hzU hne hzord
    rw [hzτ]
    exact hτt
  let S : Finset ℍ := hfinK.toFinset
  let n : ℍ → ℕ := fun τ =>
    ((meromorphicOrderAt (fun z : ℂ => f (ofComplex z)) (τ : ℂ)).untopD 0).natAbs
  obtain ⟨k, hk4, hkev, P, hP0, hPord⟩ := hample S n

  have hPan : ∀ τ : ℍ, AnalyticAt ℂ (fun z : ℂ => P (ofComplex z)) (τ : ℂ) :=
    analyticAt_comp_ofComplex (hPholo P)
  have hhmerAt : ∀ τ : ℍ,
      MeromorphicAt (fun z : ℂ => P (ofComplex z) * f (ofComplex z)) (τ : ℂ) := fun τ =>
    (hPan τ).meromorphicAt.mul (hf τ)
  have hhmer : MeromorphicOn (fun z : ℂ => P (ofComplex z) * f (ofComplex z)) {z : ℂ | 0 < z.im} :=
    fun z hz => hhmerAt ⟨z, hz⟩

  have hordh : ∀ γ ∈ Γ, ∀ τ : ℍ,
      meromorphicOrderAt (fun z : ℂ => P (ofComplex z) * f (ofComplex z)) ↑(γ • τ) =
        meromorphicOrderAt (fun z : ℂ => P (ofComplex z) * f (ofComplex z)) ↑τ := by
    intro γ hγ τ
    have hcs := UpperHalfPlane.meromorphicOrderAt_comp_smul (f := fun w : ℍ => P w * f w) (τ := τ)
      (det_pos_of_mem hγ)
    rw [← hcs]

    have hDan : AnalyticAt ℂ (fun z : ℂ => denom γ (ofComplex z) ^ k) (τ : ℂ) :=
      analyticAt_comp_ofComplex (mdifferentiable_denom_zpow γ k) τ
    have hD0 : meromorphicOrderAt (fun z : ℂ => denom γ (ofComplex z) ^ k) (τ : ℂ) = 0 := by
      rw [hDan.meromorphicOrderAt_eq, hDan.analyticOrderAt_eq_zero.mpr]
      · simp
      · simp only [ofComplex_apply]
        exact zpow_ne_zero _ (denom_ne_zero γ τ)
    have hev : (fun z : ℂ => P (γ • ofComplex z) * f (γ • ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
        (fun z : ℂ => denom γ (ofComplex z) ^ k) * (fun z : ℂ => P (ofComplex z) * f (ofComplex z)) := by
      have h2 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), f (γ • ofComplex z) = f (ofComplex z) :=
        eventually_ofComplex_iff.mpr (hinv γ hγ τ)
      filter_upwards [h2] with z hz
      rw [hz, SlashInvariantForm.slash_action_eqn'' P hγ (ofComplex z)]
      simp only [Pi.mul_apply]
      ring
    rw [meromorphicOrderAt_congr hev, meromorphicOrderAt_mul hDan.meromorphicAt (hhmerAt τ), hD0, zero_add]
  have hordK : ∀ τ ∈ K, 0 ≤ meromorphicOrderAt (fun z : ℂ => P (ofComplex z) * f (ofComplex z)) ↑τ := by
    intro τ hτK
    have hmul : meromorphicOrderAt (fun z : ℂ => P (ofComplex z) * f (ofComplex z)) ↑τ =
        meromorphicOrderAt (fun z : ℂ => P (ofComplex z)) ↑τ +
          meromorphicOrderAt (fun z : ℂ => f (ofComplex z)) ↑τ :=
      meromorphicOrderAt_mul (hPan τ).meromorphicAt (hf τ)
    rw [hmul]
    by_cases hneg : meromorphicOrderAt (fun z : ℂ => f (ofComplex z)) (τ : ℂ) < 0
    ·
      have hτS : τ ∈ S := hfinK.mem_toFinset.mpr ⟨hτK, hneg⟩
      have hP := hPord τ hτS
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hneg.ne_top
      rw [← hm] at hneg ⊢
      have hm0 : m < 0 := by exact_mod_cast hneg
      have hn : ((n τ : ℤ) : WithTop ℤ) = ((-m : ℤ) : WithTop ℤ) := by
        simp only [n, ← hm, WithTop.untopD_coe]
        congr 1
        omega
      rw [hn] at hP
      calc (0 : WithTop ℤ) = ((-m : ℤ) : WithTop ℤ) + (m : WithTop ℤ) := by norm_cast; omega
        _ ≤ _ := add_le_add hP le_rfl
    · exact add_nonneg (hPan τ).meromorphicOrderAt_nonneg (not_lt.mp hneg)
  have hord : ∀ τ : ℍ, 0 ≤ meromorphicOrderAt (fun z : ℂ => P (ofComplex z) * f (ofComplex z)) ↑τ := by
    intro τ
    obtain ⟨γ, hγ, hγK⟩ := hKcov τ
    rw [← hordh γ hγ τ]
    exact hordK _ hγK

  obtain ⟨g, hgmd, hgev⟩ : ∃ g : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧
      ∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ, g z = P z * f z := by
    let G : ℂ → ℂ := toMeromorphicNFOn (fun z : ℂ => P (ofComplex z) * f (ofComplex z)) {z : ℂ | 0 < z.im}
    have hGev : ∀ τ : ℍ, G =ᶠ[𝓝[≠] (τ : ℂ)] (fun z : ℂ => P (ofComplex z) * f (ofComplex z)) :=
      fun τ => hhmer.toMeromorphicNFOn_eq_self_on_nhdsNE τ.im_pos
    have hGan : ∀ τ : ℍ, AnalyticAt ℂ G (τ : ℂ) := by
      intro τ
      have hNF : MeromorphicNFAt G (τ : ℂ) :=
        meromorphicNFOn_toMeromorphicNFOn (fun z : ℂ => P (ofComplex z) * f (ofComplex z)) _ τ.im_pos
      refine hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
      rw [meromorphicOrderAt_congr (hGev τ)]
      exact hord τ
    refine ⟨fun τ => G τ, ?_, ?_⟩
    · rw [UpperHalfPlane.mdifferentiable_iff]
      have hGd : DifferentiableOn ℂ G {z : ℂ | 0 < z.im} :=
        fun z hz => (hGan ⟨z, hz⟩).differentiableAt.differentiableWithinAt
      refine hGd.congr fun z hz => ?_
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, UpperHalfPlane.coe_mk]
    · intro τ
      refine ((eventually_coe_iff (p := fun z : ℂ => G z = P (ofComplex z) * f (ofComplex z))).mpr
        (hGev τ)).mono fun w hw => ?_
      simpa only [ofComplex_apply] using hw

  have hslash : ∀ γ ∈ Γ, ∀ τ : ℍ, g (γ • τ) = denom γ τ ^ k * g τ := by
    intro γ hγ τ₀
    have e1 : ∀ᶠ z in 𝓝[≠] τ₀, g (γ • z) = P (γ • z) * f (γ • z) :=
      (tendsto_smul_nhdsNE γ τ₀).eventually (hgev (γ • τ₀))
    have ev : ∀ᶠ z in 𝓝[≠] τ₀, g (γ • z) = denom γ z ^ k * g z := by
      filter_upwards [e1, hinv γ hγ τ₀, hgev τ₀] with z h1 h2 h3
      rw [h1, h2, SlashInvariantForm.slash_action_eqn'' P hγ z, h3]
      ring
    have c1 : ContinuousAt (fun z : ℍ => g (γ • z)) τ₀ :=
      (hgmd.continuous.comp (continuous_const_smul γ)).continuousAt
    have c2 : ContinuousAt (fun z : ℍ => denom γ z ^ k * g z) τ₀ :=
      ((mdifferentiable_denom_zpow γ k).continuous.mul hgmd.continuous).continuousAt
    exact tendsto_nhds_unique_of_eventuallyEq (c1.tendsto.mono_left nhdsWithin_le_nhds)
      (c2.tendsto.mono_left nhdsWithin_le_nhds) ev
  let gF : ModularForm Γ k :=
    { toFun := g
      slash_action_eq' := by
        intro γ hγ
        funext τ
        have hd := Subgroup.HasDetOne.det_eq hγ
        rw [ModularForm.slash_def]
        dsimp only
        have hσ : σ γ (g (γ • τ)) = g (γ • τ) := by simp [σ, hd]
        rw [hσ, hslash γ hγ τ, hd]
        simp only [Units.val_one, abs_one, Complex.ofReal_one, one_zpow, mul_one]
        rw [zpow_neg, mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ (denom_ne_zero γ τ)), mul_comm]
      holo' := hgmd
      bdd_at_cusps' := fun hc => absurd hc (hcusp _) }
  have hgF : (gF : ℍ → ℂ) = g := rfl

  have hPs : P.toHolRing ≠ 0 := fun h0 => hP0 ((ModularForm.toHolRing_eq_zero_iff P).1 h0)
  refine ⟨⟨algebraMap ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing) gF.toHolRing /
      algebraMap ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing) P.toHolRing, k, gF, P, hP0, rfl⟩, ?_⟩
  intro τ
  have h0 := (ModularCurve.automorphicField_realize_laws Γ).1 gF.toHolRing P.toHolRing hPs τ
  have hPne : ∀ᶠ z in 𝓝[≠] τ, P z ≠ 0 := by
    by_contra hne
    have hfr : ∃ᶠ z in 𝓝[≠] τ, P z = 0 := by
      simpa only [Filter.not_eventually, not_not] using hne
    exact hP0 (UpperHalfPlane.eq_zero_of_frequently (hPholo P) hfr)
  filter_upwards [h0, hPne, hgev τ] with z hz hPz hgz
  change ModularCurve.merRealize (algebraMap ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing) gF.toHolRing /
      algebraMap ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing) P.toHolRing) z = f z
  rw [hz, ModularForm.coe_toHolRing, ModularForm.coe_toHolRing, hgF, hgz]
  exact mul_div_cancel_left₀ (f z) hPz

end
end S_ModularCurve_exists_realize_eventuallyEq_of_isCompact
end P2MW
export P2MW.S_ModularCurve_exists_realize_eventuallyEq_of_isCompact (solution)
