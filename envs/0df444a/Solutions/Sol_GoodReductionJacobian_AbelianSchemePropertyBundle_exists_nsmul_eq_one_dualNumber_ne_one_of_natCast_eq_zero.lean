-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_nsmul_eq_one_dualNumber_ne_one_of_natCast_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/65942e74-db68-537d-867f-f9554e22b090

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_natCast_smul_of_forall_add_eq_mul
import Theorems.Thm_CerednikDrinfeld_QM_exists_injective_range_iff_isTangentVector
import Theorems.Thm_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_preimage_singleton_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_nsmul_eq_one_dualNumber_ne_one_of_natCast_eq_zero
p2m_attr_erase "instance" "AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing"
p2m_attr_erase "simp" "AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
p2m_open_scoped "BigOperators CategoryTheory.MonoidalCategory"

open CerednikDrinfeld.QM in
set_option maxHeartbeats 3200000 in
theorem solution
    {K : Type} [Field K] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of K)} (L : RelativeGroupLaw K f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of K)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g) (hg : 0 < g)
    (n : ℕ) (hn : (n : K) = 0) :
    ∃ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K)))) f,
      L.nsmul _ n y = L.one _ ∧
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ y.1 = (L.one (𝟙 (Spec (CommRingCat.of K)))).1 ∧
      y ≠ L.one _ := by
  classical
  haveI : Smooth f := hA.smooth

  let s₀ : ↥(Spec (CommRingCat.of K)) := default
  have huniv : f.base ⁻¹' {s₀} = Set.univ := Set.eq_univ_of_forall (fun a => Subsingleton.elim _ _)
  haveI : ConnectedSpace ↥A := connectedSpace_iff_univ.mpr (huniv ▸ hA.connectedFibres s₀)
  obtain ⟨m, hm⟩ := AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace f
  haveI := hm
  have hmg : m = g := by
    have h1 := AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq f m s₀ (hA.connectedFibres s₀).nonempty
    have h2 := hdim s₀
    rw [h1] at h2
    exact_mod_cast h2
  subst hmg

  obtain ⟨V, _, _, τ, hinj, hrange, hadd, hsmul⟩ := exists_injective_range_iff_isTangentVector L K (RingHom.id K)
  have hfin : Module.finrank K V = m :=
    finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension L m K (RingHom.id K) V τ hinj hrange hadd hsmul
  obtain ⟨w, hw⟩ : ∃ w : V, w ≠ 0 := by
    by_contra h
    push_neg at h
    haveI : Subsingleton V := ⟨fun a b => by rw [h a, h b]⟩
    have : Module.finrank K V = 0 := Module.finrank_zero_of_subsingleton
    omega

  letI := L.pointGroup (tangentBase K (RingHom.id K))
  have h0 : τ 0 = L.one (tangentBase K (RingHom.id K)) := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact (mul_left_cancel (a := τ 0) (h.symm.trans (mul_one (τ 0)).symm : τ 0 * τ 0 = τ 0 * 1)).symm ▸ rfl
  have hM1 := (GoodReductionJacobian.RelativeGroupLaw.nsmul_eq_natCast_smul_of_forall_add_eq_mul L K (RingHom.id K) V τ hadd n w).2 hn
  have htv : IsTangentVector L K (RingHom.id K) (τ w) := (hrange (τ w)).mp ⟨w, rfl⟩
  have eT : tangentBase K (RingHom.id K) = (Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K)))) := by
    unfold tangentBase; rw [RingHom.comp_id]
  have eG : geomPoint K (RingHom.id K) = 𝟙 (Spec (CommRingCat.of K)) := by
    unfold geomPoint; rw [CommRingCat.ofHom_id, Spec.map_id]

  have trN : ∀ {t₁ t₂ : Spec (CommRingCat.of (DualNumber K)) ⟶ Spec (CommRingCat.of K)} (e : t₁ = t₂) (P : SchemeHomOver t₁ f),
      L.nsmul t₁ n P = L.one t₁ → L.nsmul t₂ n ⟨P.1, e ▸ P.2⟩ = L.one t₂ := by
    intro t₁ t₂ e P h; subst e; exact h
  have trO : ∀ {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of K)} (e : t₁ = t₂), (L.one t₁).1 = (L.one t₂).1 := by
    intro T t₁ t₂ e; subst e; rfl
  refine ⟨⟨(τ w).1, eT ▸ (τ w).2⟩, trN eT (τ w) hM1, ?_, ?_⟩
  · show tangentZero K ≫ (τ w).1 = _
    rw [htv, trO eG]
  · intro heq
    apply hw
    apply hinj
    rw [h0]
    apply Subtype.ext
    have := congrArg Subtype.val heq
    exact this.trans (trO eT).symm

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_nsmul_eq_one_dualNumber_ne_one_of_natCast_eq_zero
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_nsmul_eq_one_dualNumber_ne_one_of_natCast_eq_zero (solution)
