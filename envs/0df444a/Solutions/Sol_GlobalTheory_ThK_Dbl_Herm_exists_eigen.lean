-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Herm.exists_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:41:20.253979+00:00
-- url     : https://prove2.me/submissions/5fa517eb-e8f8-4726-803e-77d9ce7e2e76

import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_SpanOrbitStab
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_HermAbs
import Theorems.Thm_GlobalTheory_ThK_Dbl_Herm_exists_rep
import Theorems.Thm_PositivityTheory_ThKF_Abs_mem_orb
import Theorems.Thm_PositivityTheory_ThKF_Abs_orth_stab
import Theorems.Thm_PositivityTheory_ThKF_Abs_span_orbit_stab


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Herm
open scoped InnerProductSpace
open PositivityTheory.ThKF.Abs
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
namespace GlobalTheory.ThK.Dbl.Herm
theorem _root_.solution {K : Type} [Group K] (κ : K →* Module.End ℂ U) (hi : ∀ k x y, ⟪κ k x, κ k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hf : ∀ x, FiniteDimensional ℂ (orb κ x)) {ι : Type} [Finite ι] (l : ι → U →ₗ[ℂ] ℂ)
    (hl : ∀ x, (∀ i k, l i (κ k x) = 0) → x = 0) (b : U →ₗ⋆[ℂ] U →ₗ[ℂ] ℂ) (hb : ∀ k x y, b (κ k x) (κ k y) = b x y)
    (f : U) (h0 : f ≠ 0) : ∃ (x : U) (c : ℂ), x ≠ 0 ∧ ∀ y, b x y = c * ⟪x, y⟫_ℂ := by
  have := hf f
  have : FiniteDimensional ℂ (homsF κ f) := by
    let ev : homsF κ f →ₗ[ℂ] (ι → Module.Dual ℂ (orb κ f)) :=
      LinearMap.pi fun i => (LinearMap.llcomp ℂ _ _ _ (l i)) ∘ₗ (homsF κ f).subtype
    refine Module.Finite.of_injective ev ((injective_iff_map_eq_zero ev).2 fun L hL => Subtype.ext (LinearMap.ext fun x => ?_))
    refine hl _ fun i k => ?_
    rw [← L.2 k x]
    exact LinearMap.congr_fun (congrFun hL i) _
  let Z : Submodule ℂ U := Submodule.map₂ (LinearMap.id : (orb κ f →ₗ[ℂ] U) →ₗ[ℂ] _) (homsF κ f) ⊤
  have fZ : FiniteDimensional ℂ Z := Module.Finite.iff_fg.2
    (Submodule.FG.map₂ _ (Module.Finite.iff_fg.1 inferInstance) (Module.Finite.fg_top))
  have mZ : ∀ L ∈ homsF κ f, ∀ x, L x ∈ Z := fun L hL x => Submodule.apply_mem_map₂ _ hL trivial
  have sZ : ∀ k, ∀ z ∈ Z, κ k z ∈ Z := fun k => show Z ≤ Z.comap (κ k) from
    Submodule.map₂_le.2 fun L hL x _ => by
      show κ k (L x) ∈ Z
      rw [← hL k x]; exact mZ L hL _
  have orth : ∀ y ∈ Zᗮ, ∀ z ∈ Z, b z y = 0 := fun y hy => by
    have := hf y
    have yZ : orb κ y ≤ Zᗮ := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact orth_stab κ hi Z sZ k y hy)
    obtain ⟨T, hT⟩ := exists_rep b (orb κ y)
    have eq : ∀ k x, (T (κ k x) : U) = κ k (T x) := fun k x => by
      have : T (κ k x) = ⟨κ k (T x), span_orbit_stab κ y k _ (T x).2⟩ := ext_inner_right ℂ fun u => by
        have e : (u : U) = κ k (κ k⁻¹ u) := by rw [← Module.End.mul_apply, ← map_mul]; simp
        show ⟪(T (κ k x) : U), (u : U)⟫_ℂ = ⟪κ k (T x), (u : U)⟫_ℂ
        rw [hT _ _ u.2, e, hb, hi, hT _ _ (span_orbit_stab κ y k⁻¹ _ u.2)]
      rw [this]
    refine show Z ≤ LinearMap.ker (b.flip y) from Submodule.map₂_le.2 fun L hL x _ => ?_
    show b (L x) y = 0
    have h1 : (T (L x) : U) ∈ Z := mZ ((orb κ y).subtype ∘ₗ T ∘ₗ L) (fun k x => by
      show (T (L _) : U) = κ k (T (L x))
      rw [hL k x, eq]) x
    rw [← hT _ _ (mem_orb κ y)]
    exact hy _ h1
  obtain ⟨T, hT⟩ := exists_rep b Z
  have : Nontrivial Z := ⟨⟨f, mZ (orb κ f).subtype (fun _ _ => rfl) ⟨f, mem_orb κ f⟩⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T ∘ₗ Z.subtype)
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  refine ⟨x, starRingEnd ℂ c, fun h => hx.2 (Subtype.ext h), fun y => ?_⟩
  have e : T x = c • x := hx.apply_eq_smul
  have hy := Z.sub_starProjection_mem_orthogonal y
  have e1 := orth _ hy x x.2
  have e2 := hy _ x.2
  rw [map_sub, sub_eq_zero] at e1
  rw [inner_sub_right, sub_eq_zero] at e2
  rw [e1, e2, ← hT _ _ (Z.starProjection_apply_mem y), e, Submodule.coe_smul, inner_smul_left]
end GlobalTheory.ThK.Dbl.Herm
