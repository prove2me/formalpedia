-- Prove2me | solution 1 for HopfAlgebra.surjective_of_bijective_of_bijOn_hopfKer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f4abd103-8d18-54e6-8b84-375b56f00042

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_isHopfGalois_of_surjective
import Theorems.Thm_HopfAlgebra_finite_projective_hopfKer_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_surjective_of_bijective_of_bijOn_hopfKer

set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace HopfAlgebra
p2m_export "HopfAlgebra" "coaction hopfKer canMap canMap_tmul balancingRelations IsHopfGalois isHopfGalois_of_surjective finite_projective_hopfKer_of_surjective"
namespace FiveLemmaEpi
p2m_open "HopfAlgebra"

p2m_open "HopfAlgebra P2MW.S_HopfAlgebra_surjective_of_bijective_of_bijOn_hopfKer.HopfAlgebra TensorProduct"

section General

variable {R : Type u} [CommRing R]
variable {H : Type v} [CommRing H] [HopfAlgebra R H]
variable {H' : Type v} [CommRing H'] [HopfAlgebra R H']
variable {Q : Type w} [CommRing Q] [HopfAlgebra R Q]
variable {Q' : Type w} [CommRing Q'] [HopfAlgebra R Q']
variable (φ : H →ₐc[R] H') (π : H →ₐc[R] Q) (π' : H' →ₐc[R] Q') (ψ : Q →ₐc[R] Q')

noncomputable abbrev cmp : H ⊗[R] Q →ₐ[R] H' ⊗[R] Q' :=
  Algebra.TensorProduct.map (φ : H →ₐ[R] H') (ψ : Q →ₐ[R] Q')

theorem coaction_comp
    (hcomm : (π' : H' →ₐ[R] Q').comp (φ : H →ₐ[R] H') = (ψ : Q →ₐ[R] Q').comp (π : H →ₐ[R] Q)) :
    (coaction π').comp (φ : H →ₐ[R] H') = (cmp φ ψ).comp (coaction π) := by
  unfold coaction cmp
  calc ((Algebra.TensorProduct.map (AlgHom.id R H') (π' : H' →ₐ[R] Q')).comp (Bialgebra.comulAlgHom R H')).comp
          (φ : H →ₐ[R] H')
        = (Algebra.TensorProduct.map (AlgHom.id R H') (π' : H' →ₐ[R] Q')).comp
            ((Bialgebra.comulAlgHom R H').comp (φ : H →ₐ[R] H')) := by rw [AlgHom.comp_assoc]
    _ = (Algebra.TensorProduct.map (AlgHom.id R H') (π' : H' →ₐ[R] Q')).comp
            ((Algebra.TensorProduct.map (φ : H →ₐ[R] H') (φ : H →ₐ[R] H')).comp
              (Bialgebra.comulAlgHom R H)) := by rw [BialgHom.map_comp_comulAlgHom φ]
    _ = (Algebra.TensorProduct.map ((AlgHom.id R H').comp (φ : H →ₐ[R] H'))
            ((π' : H' →ₐ[R] Q').comp (φ : H →ₐ[R] H'))).comp (Bialgebra.comulAlgHom R H) := by
          rw [← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp]
    _ = (Algebra.TensorProduct.map ((φ : H →ₐ[R] H').comp (AlgHom.id R H))
            ((ψ : Q →ₐ[R] Q').comp (π : H →ₐ[R] Q))).comp (Bialgebra.comulAlgHom R H) := by
          rw [AlgHom.id_comp, AlgHom.comp_id, hcomm]
    _ = ((Algebra.TensorProduct.map (φ : H →ₐ[R] H') (ψ : Q →ₐ[R] Q')).comp
            (Algebra.TensorProduct.map (AlgHom.id R H) (π : H →ₐ[R] Q))).comp
              (Bialgebra.comulAlgHom R H) := by rw [← Algebra.TensorProduct.map_comp]
    _ = _ := by rw [AlgHom.comp_assoc]

theorem coaction_apply_map
    (hcomm : (π' : H' →ₐ[R] Q').comp (φ : H →ₐ[R] H') = (ψ : Q →ₐ[R] Q').comp (π : H →ₐ[R] Q)) (a : H) :
    coaction π' (φ a) = cmp φ ψ (coaction π a) :=
  congrArg (fun g : H →ₐ[R] H' ⊗[R] Q' => g a) (coaction_comp φ π π' ψ hcomm)

theorem cmp_canMap
    (hcomm : (π' : H' →ₐ[R] Q').comp (φ : H →ₐ[R] H') = (ψ : Q →ₐ[R] Q').comp (π : H →ₐ[R] Q))
    (w : H ⊗[R] H) :
    cmp φ ψ (canMap π w) =
      canMap π' (TensorProduct.map (φ : H →ₐ[R] H').toLinearMap (φ : H →ₐ[R] H').toLinearMap w) := by
  induction w with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, map_add, map_add, hy]
  | tmul x y =>
      rw [canMap_tmul, map_mul, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
        canMap_tmul, ← coaction_apply_map φ π π' ψ hcomm y]
      congr 1
      simp [cmp]

noncomputable def gam : H' ⊗[R] H →ₗ[R] H' ⊗[R] Q' :=
  canMap π' ∘ₗ (φ : H →ₐ[R] H').toLinearMap.lTensor H'

theorem gam_apply (z : H' ⊗[R] H) : gam φ π' z = canMap π' ((φ : H →ₐ[R] H').toLinearMap.lTensor H' z) := rfl

@[scoped simp] theorem gam_tmul (b : H') (a : H) : gam φ π' (b ⊗ₜ[R] a) = (b ⊗ₜ[R] (1 : Q')) * coaction π' (φ a) := by
  rw [gam_apply, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, canMap_tmul]
  rfl

theorem tmul_one_mul_gam (b : H') (z : H' ⊗[R] H) :
    (b ⊗ₜ[R] (1 : Q')) * gam φ π' z = gam φ π' ((b ⊗ₜ[R] (1 : H)) * z) := by
  induction z with
  | zero => simp
  | add x y hx hy => rw [map_add, mul_add, hx, hy, mul_add, map_add]
  | tmul x y =>
      rw [gam_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, gam_tmul, ← mul_assoc,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem gam_surjective
    (hcomm : (π' : H' →ₐ[R] Q').comp (φ : H →ₐ[R] H') = (ψ : Q →ₐ[R] Q').comp (π : H →ₐ[R] Q))
    (hcan : Function.Surjective (canMap π)) (hπ : Function.Surjective π) (hψ : Function.Surjective ψ) :
    Function.Surjective (gam φ π') := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro z -
  induction z with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul b q' =>
      obtain ⟨q, rfl⟩ := hψ q'
      obtain ⟨a, rfl⟩ := hπ q
      obtain ⟨w, hw⟩ := hcan ((1 : H) ⊗ₜ[R] π a)

      have h1 : (1 : H') ⊗ₜ[R] ψ (π a) = gam φ π' ((φ : H →ₐ[R] H').toLinearMap.rTensor H w) := by
        have e1 : cmp φ ψ ((1 : H) ⊗ₜ[R] π a) = (1 : H') ⊗ₜ[R] ψ (π a) := by
          simp [cmp]
        have e2 : ((φ : H →ₐ[R] H').toLinearMap.lTensor H') (((φ : H →ₐ[R] H').toLinearMap.rTensor H) w) =
            TensorProduct.map (φ : H →ₐ[R] H').toLinearMap (φ : H →ₐ[R] H').toLinearMap w := by
          rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor]
        rw [← e1, ← hw, cmp_canMap φ π π' ψ hcomm, gam_apply, e2]
      have h2 : b ⊗ₜ[R] ψ (π a) = (b ⊗ₜ[R] (1 : Q')) * ((1 : H') ⊗ₜ[R] ψ (π a)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [h2, h1, tmul_one_mul_gam]
      exact LinearMap.mem_range_self _ _

noncomputable def resHopfKer (hmaps : Set.MapsTo φ (hopfKer π) (hopfKer π')) :
    ↥(hopfKer π) →ₐ[R] ↥(hopfKer π') :=
  ((φ : H →ₐ[R] H').comp (hopfKer π).val).codRestrict (hopfKer π') (fun x => hmaps x.2)

@[scoped simp] theorem coe_resHopfKer (hmaps : Set.MapsTo φ (hopfKer π) (hopfKer π')) (x : ↥(hopfKer π)) :
    (resHopfKer φ π π' hmaps x : H') = φ x := rfl

theorem resHopfKer_bijective (hφ : Set.BijOn φ (hopfKer π) (hopfKer π')) :
    Function.Bijective (resHopfKer φ π π' hφ.mapsTo) := by
  refine ⟨fun a b hab => Subtype.ext (hφ.injOn a.2 b.2 ?_), fun y => ?_⟩
  · have := congrArg Subtype.val hab
    simpa using this
  · obtain ⟨x, hx, hxy⟩ := hφ.surjOn y.2
    exact ⟨⟨x, hx⟩, Subtype.ext (by simpa using hxy)⟩

noncomputable def eqvHopfKer (hφ : Set.BijOn φ (hopfKer π) (hopfKer π')) :
    ↥(hopfKer π) ≃ₐ[R] ↥(hopfKer π') :=
  AlgEquiv.ofBijective (resHopfKer φ π π' hφ.mapsTo) (resHopfKer_bijective φ π π' hφ)

@[scoped simp] theorem coe_eqvHopfKer (hφ : Set.BijOn φ (hopfKer π) (hopfKer π')) (x : ↥(hopfKer π)) :
    (eqvHopfKer φ π π' hφ x : H') = φ x := rfl

theorem map_coe_eqvHopfKer_symm (hφ : Set.BijOn φ (hopfKer π) (hopfKer π')) (s : ↥(hopfKer π')) :
    φ ((eqvHopfKer φ π π' hφ).symm s : H) = (s : H') := by
  rw [← coe_eqvHopfKer φ π π' hφ, AlgEquiv.apply_symm_apply]

end General

section Descent

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
variable {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Finite R H'] [Module.Flat R H']
variable {Q : Type w} [CommRing Q] [HopfAlgebra R Q] [Module.Finite R Q] [Module.Flat R Q]
variable {Q' : Type w} [CommRing Q'] [HopfAlgebra R Q'] [Module.Finite R Q'] [Module.Flat R Q']

theorem main (φ : H →ₐc[R] H') (π : H →ₐc[R] Q) (π' : H' →ₐc[R] Q') (ψ : Q →ₐc[R] Q')
    (hπ : Function.Surjective π) (hπ' : Function.Surjective π')
    (hcomm : (π' : H' →ₐ[R] Q').comp (φ : H →ₐ[R] H') = (ψ : Q →ₐ[R] Q').comp (π : H →ₐ[R] Q))
    (hψ : Function.Bijective ψ)
    (hφ : Set.BijOn φ (HopfAlgebra.hopfKer π) (HopfAlgebra.hopfKer π')) :
    Function.Surjective φ := by
  classical

  haveI : Module.Free R Q := Module.free_of_finite_type_torsion_free'
  haveI : Module.Free R Q' := Module.free_of_finite_type_torsion_free'

  have hG : IsHopfGalois π := HopfAlgebra.isHopfGalois_of_surjective π hπ
  have hG' : IsHopfGalois π' := HopfAlgebra.isHopfGalois_of_surjective π' hπ'
  obtain ⟨hfin', hproj'⟩ := HopfAlgebra.finite_projective_hopfKer_of_surjective π' hπ'
  set S := hopfKer π with hSdef
  set S' := hopfKer π' with hS'def
  haveI : Module.Finite ↥S' H' := hfin'
  haveI : Module.Projective ↥S' H' := hproj'

  haveI : Module.FaithfullyFlat ↥S' H' := by
    refine ⟨fun m hm htop => ?_⟩
    have hle : (⊤ : Submodule ↥S' H') ≤ m • ⊤ := by rw [htop]
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤
      Module.Finite.fg_top hle
    have hr0 : r = 0 := by
      have h1 := hr 1 Submodule.mem_top
      rw [Algebra.smul_def, mul_one] at h1
      exact Subtype.ext (by simpa using h1)
    rw [hr0, zero_sub, neg_mem_iff] at hr1
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 hr1)

  set e := eqvHopfKer φ π π' hφ with hedef
  letI algS'H : Algebra ↥S' H := ((S.val).comp (e.symm : ↥S' →ₐ[R] ↥S)).toRingHom.toAlgebra
  have halg : ∀ s : ↥S', algebraMap (↥S') H s = ((e.symm s : ↥S) : H) := fun s => rfl
  haveI : IsScalarTower R ↥S' H := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [halg, AlgEquiv.commutes]
    rfl)

  let φS : H →ₗ[↥S'] H' :=
    { toFun := φ
      map_add' := fun a b => map_add φ a b
      map_smul' := fun s a => by
        rw [RingHom.id_apply, Algebra.smul_def, halg, map_mul, Algebra.smul_def]
        congr 1
        exact map_coe_eqvHopfKer_symm φ π π' hφ s }
  have hφS : ∀ a, φS a = φ a := fun a => rfl

  suffices hsurj : Function.Surjective (φS.lTensor H') by
    have := (Module.FaithfullyFlat.lTensor_surjective_iff_surjective (R := ↥S') (M := H') φS).1 hsurj
    intro y
    obtain ⟨x, hx⟩ := this y
    exact ⟨x, hx⟩

  haveI : SMulCommClass (↥S') R H' := ⟨fun s r h => by
    simp only [Algebra.smul_def]
    rw [mul_left_comm]⟩
  let θH : H' ⊗[R] H →ₗ[↥S'] H' ⊗[↥S'] H := TensorProduct.mapOfCompatibleSMul (↥S') R (↥S') H' H
  let θH' : H' ⊗[R] H' →ₗ[↥S'] H' ⊗[↥S'] H' := TensorProduct.mapOfCompatibleSMul (↥S') R (↥S') H' H'
  have hθH'surj : Function.Surjective θH' := TensorProduct.mapOfCompatibleSMul_surjective _ _ _ _ _

  have hnat : ∀ w : H' ⊗[R] H, θH' ((φ : H →ₐ[R] H').toLinearMap.lTensor H' w) = φS.lTensor H' (θH w) := by
    intro w
    induction w with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | tmul b a => rfl

  have hbal : ∀ w ∈ Submodule.span R (balancingRelations π'), θH' w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨a, s, b, hs, rfl⟩ := hx
        simp only [θH', map_sub]
        rw [sub_eq_zero, mul_comm a s]
        change ((⟨s, hs⟩ : ↥S') • a) ⊗ₜ[↥S'] b = a ⊗ₜ[↥S'] ((⟨s, hs⟩ : ↥S') • b)
        exact TensorProduct.smul_tmul _ _ _
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul r x _ hx =>
        rw [← algebraMap_smul (↥S') r x, LinearMap.map_smul, hx, smul_zero]

  have hker : ∀ w w' : H' ⊗[R] H', canMap π' w = canMap π' w' → θH' w = θH' w' := by
    intro w w' hww'
    have h0 : canMap π' (w - w') = 0 := by rw [map_sub, hww', sub_self]
    have h1 := hbal _ (hG'.2 _ h0)
    rwa [map_sub, sub_eq_zero] at h1

  have hgam : Function.Surjective (gam φ π') :=
    gam_surjective φ π π' ψ hcomm hG.1 hπ hψ.2

  intro z
  obtain ⟨w, rfl⟩ := hθH'surj z
  obtain ⟨w₀, hw₀⟩ := hgam (canMap π' w)
  refine ⟨θH w₀, ?_⟩
  rw [← hnat, hker _ _ hw₀.symm]

end Descent

end HopfAlgebra.FiveLemmaEpi
p2m_reactivate "P2MW.S_HopfAlgebra_surjective_of_bijective_of_bijOn_hopfKer.HopfAlgebra P2MW.S_HopfAlgebra_surjective_of_bijective_of_bijOn_hopfKer.HopfAlgebra.FiveLemmaEpi"
p2m_reactivate "P2MW.S_HopfAlgebra_surjective_of_bijective_of_bijOn_hopfKer.HopfAlgebra"

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Finite R H'] [Module.Flat R H']
    {Q : Type w} [CommRing Q] [HopfAlgebra R Q] [Module.Finite R Q] [Module.Flat R Q]
    {Q' : Type w} [CommRing Q'] [HopfAlgebra R Q'] [Module.Finite R Q'] [Module.Flat R Q']
    (φ : H →ₐc[R] H') (π : H →ₐc[R] Q) (π' : H' →ₐc[R] Q') (ψ : Q →ₐc[R] Q')
    (hπ : Function.Surjective π) (hπ' : Function.Surjective π')
    (hcomm : (π' : H' →ₐ[R] Q').comp (φ : H →ₐ[R] H') = (ψ : Q →ₐ[R] Q').comp (π : H →ₐ[R] Q))
    (hψ : Function.Bijective ψ)
    (hφ : Set.BijOn φ (HopfAlgebra.hopfKer π) (HopfAlgebra.hopfKer π')) :
    Function.Surjective φ :=
  HopfAlgebra.FiveLemmaEpi.main φ π π' ψ hπ hπ' hcomm hψ hφ

end S_HopfAlgebra_surjective_of_bijective_of_bijOn_hopfKer
end P2MW
export P2MW.S_HopfAlgebra_surjective_of_bijective_of_bijOn_hopfKer (solution)
