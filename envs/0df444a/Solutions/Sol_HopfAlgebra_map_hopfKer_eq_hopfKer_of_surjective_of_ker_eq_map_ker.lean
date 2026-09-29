-- Prove2me | solution 1 for HopfAlgebra.map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/302228ee-d4a2-54a9-a8e1-f736959c8f4e

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_HopfTower
import Theorems.Thm_HopfAlgebra_isHopfGalois_iff_ker_le_span_of_surjective
import Theorems.Thm_HopfAlgebra_isHopfGalois_of_surjective
import Theorems.Thm_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open scoped TensorProduct
open Function WithConv Coalgebra

universe u v w x y

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mul_antipode_rTensor_comul mul_antipode_lTensor_comul coaction_apply hopfKer mem_hopfKer_iff IsHopfGalois HopfKerHopf.antipode_mem HopfKerHopf.ι₂_tmul HopfKerHopf.comul_coe_mem_range IsHopfTower mem_augIdeal IsHopfSubalgebra HopfTower.augIdealMap HopfTower.fwdAux HopfTower.fwdAux_algebraMap HopfTower.galoisEquiv HopfTower.galoisEquiv_tmul isHopfGalois_iff_ker_le_span_of_surjective isHopfGalois_of_surjective faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem"
namespace SecondIso
p2m_open "HopfAlgebra"

section Upgrade

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [HopfAlgebra k A]
variable {Q : Type w} [CommRing Q] [Bialgebra k Q] [Module.Finite k Q]
variable (f : A →ₐc[k] Q) (hf : Surjective f)

abbrev EQ (Q : Type w) [CommRing Q] [Bialgebra k Q] : Type _ := WithConv (Q →ₗ[k] Q)

abbrev FQ (A : Type v) [CommRing A] [HopfAlgebra k A] (Q : Type w) [CommRing Q] [Bialgebra k Q] :
    Type _ := WithConv (A →ₗ[k] Q)

def pre : EQ (k := k) Q →* FQ (k := k) A Q where
  toFun g := toConv (g.ofConv ∘ₗ (f : A →ₗc[k] Q).toLinearMap)
  map_one' := by
    refine WithConv.ext (LinearMap.ext fun a => ?_)
    simp only [LinearMap.comp_apply, LinearMap.convOne_apply]
    change algebraMap k Q (Coalgebra.counit (f a)) = algebraMap k Q (Coalgebra.counit a)
    rw [CoalgHomClass.counit_comp_apply]
  map_mul' g h := by
    refine WithConv.ext ?_
    exact LinearMap.convMul_comp_coalgHom_distrib g h (f : A →ₗc[k] Q)

theorem pre_apply (g : EQ (k := k) Q) (a : A) : (pre f g).ofConv a = g.ofConv (f a) := rfl

include hf in
theorem pre_injective : Injective (pre f) := by
  intro g h hgh
  refine WithConv.ext (LinearMap.ext fun q => ?_)
  obtain ⟨a, rfl⟩ := hf q
  have := congrArg (fun e : FQ (k := k) A Q => e.ofConv a) hgh
  exact this

def uu : FQ (k := k) A Q := toConv (f : A →ₐ[k] Q).toLinearMap

def vv : FQ (k := k) A Q := toConv ((f : A →ₐ[k] Q).toLinearMap ∘ₗ HopfAlgebra.antipode k (A := A))

theorem antipode_mul_id :
    (toConv (HopfAlgebra.antipode k (A := A)) * toConv (LinearMap.id : A →ₗ[k] A)) = 1 := by
  apply WithConv.ofConv_injective
  rw [LinearMap.convMul_def, ofConv_toConv, ofConv_toConv, ofConv_toConv, LinearMap.convOne_def,
    ofConv_toConv]
  exact HopfAlgebra.mul_antipode_rTensor_comul

theorem id_mul_antipode :
    (toConv (LinearMap.id : A →ₗ[k] A) * toConv (HopfAlgebra.antipode k (A := A))) = 1 := by
  apply WithConv.ofConv_injective
  rw [LinearMap.convMul_def, ofConv_toConv, ofConv_toConv, ofConv_toConv, LinearMap.convOne_def,
    ofConv_toConv]
  exact HopfAlgebra.mul_antipode_lTensor_comul

theorem vv_mul_uu : vv f * uu f = 1 := by
  have h := LinearMap.algHom_comp_convMul_distrib (f : A →ₐ[k] Q)
    (toConv (HopfAlgebra.antipode k (A := A))) (toConv (LinearMap.id : A →ₗ[k] A))
  rw [antipode_mul_id, ofConv_toConv, ofConv_toConv, LinearMap.comp_id] at h
  apply WithConv.ofConv_injective
  rw [vv, uu, ← h, LinearMap.convOne_def, LinearMap.convOne_def, ofConv_toConv, ofConv_toConv]
  refine LinearMap.ext fun a => ?_
  simp only [LinearMap.comp_apply]
  exact (f : A →ₐ[k] Q).commutes _

theorem uu_mul_vv : uu f * vv f = 1 := by
  have h := LinearMap.algHom_comp_convMul_distrib (f : A →ₐ[k] Q)
    (toConv (LinearMap.id : A →ₗ[k] A)) (toConv (HopfAlgebra.antipode k (A := A)))
  rw [id_mul_antipode, ofConv_toConv, ofConv_toConv, LinearMap.comp_id] at h
  apply WithConv.ofConv_injective
  rw [vv, uu, ← h, LinearMap.convOne_def, LinearMap.convOne_def, ofConv_toConv, ofConv_toConv]
  refine LinearMap.ext fun a => ?_
  simp only [LinearMap.comp_apply]
  exact (f : A →ₐ[k] Q).commutes _

theorem pre_id : pre f (toConv LinearMap.id) = uu f := rfl

def mulLeftId : EQ (k := k) Q →ₗ[k] EQ (k := k) Q where
  toFun g := toConv LinearMap.id * g
  map_add' g h := mul_add _ _ _
  map_smul' c g := by
    refine WithConv.ext (LinearMap.ext fun q => ?_)
    rw [RingHom.id_apply, LinearMap.convMul_apply, ofConv_smul, TensorProduct.map_smul_right,
      LinearMap.smul_apply, map_smul, ofConv_smul, LinearMap.smul_apply, LinearMap.convMul_apply]

def mulRightId : EQ (k := k) Q →ₗ[k] EQ (k := k) Q where
  toFun g := g * toConv LinearMap.id
  map_add' g h := add_mul _ _ _
  map_smul' c g := by
    refine WithConv.ext (LinearMap.ext fun q => ?_)
    rw [RingHom.id_apply, LinearMap.convMul_apply, ofConv_smul, TensorProduct.map_smul_left,
      LinearMap.smul_apply, map_smul, ofConv_smul, LinearMap.smul_apply, LinearMap.convMul_apply]

include hf in
theorem mulLeftId_injective : Injective (mulLeftId (k := k) (Q := Q)) := by
  intro g h hgh
  change toConv LinearMap.id * g = toConv LinearMap.id * h at hgh
  apply pre_injective f hf
  have := congrArg (pre f) hgh
  rw [map_mul, map_mul, pre_id] at this
  have h2 := congrArg (fun z => vv f * z) this
  simp only [← mul_assoc, vv_mul_uu, one_mul] at h2
  exact h2

include hf in
theorem mulRightId_injective : Injective (mulRightId (k := k) (Q := Q)) := by
  intro g h hgh
  change g * toConv LinearMap.id = h * toConv LinearMap.id at hgh
  apply pre_injective f hf
  have := congrArg (pre f) hgh
  rw [map_mul, map_mul, pre_id] at this
  have h2 := congrArg (fun z => z * vv f) this
  simp only [mul_assoc, uu_mul_vv, mul_one] at h2
  exact h2

scoped instance : Module.Finite k (EQ (k := k) Q) :=
  Module.Finite.equiv (WithConv.linearEquiv (R := k) (Q →ₗ[k] Q)).symm

include hf in

theorem exists_antipode :
    ∃ S : EQ (k := k) Q, toConv LinearMap.id * S = 1 ∧ S * toConv LinearMap.id = 1 := by
  obtain ⟨S₁, hS₁⟩ := (LinearMap.injective_iff_surjective.1 (mulLeftId_injective f hf)) 1
  obtain ⟨S₂, hS₂⟩ := (LinearMap.injective_iff_surjective.1 (mulRightId_injective f hf)) 1
  change toConv LinearMap.id * S₁ = 1 at hS₁
  change S₂ * toConv LinearMap.id = 1 at hS₂
  have : S₁ = S₂ := (left_inv_eq_right_inv hS₂ hS₁).symm
  exact ⟨S₁, hS₁, this ▸ hS₂⟩

def antipodeQ : Q →ₗ[k] Q := (exists_antipode f hf).choose.ofConv

theorem toConv_antipodeQ : toConv (antipodeQ f hf) = (exists_antipode f hf).choose := rfl

theorem id_mul_antipodeQ : toConv LinearMap.id * toConv (antipodeQ f hf) = 1 := by
  rw [toConv_antipodeQ]; exact (exists_antipode f hf).choose_spec.1

theorem antipodeQ_mul_id : toConv (antipodeQ f hf) * toConv LinearMap.id = 1 := by
  rw [toConv_antipodeQ]; exact (exists_antipode f hf).choose_spec.2

@[reducible] private def _root_.HopfAlgebra.SecondIso.hopfAlgebra : HopfAlgebra k Q :=
  { (‹Bialgebra k Q›) with
    antipode := antipodeQ f hf
    mul_antipode_rTensor_comul := by
      have h := congrArg WithConv.ofConv (antipodeQ_mul_id f hf)
      rw [LinearMap.convMul_def, ofConv_toConv, ofConv_toConv, ofConv_toConv,
        LinearMap.convOne_def, ofConv_toConv] at h
      exact h
    mul_antipode_lTensor_comul := by
      have h := congrArg WithConv.ofConv (id_mul_antipodeQ f hf)
      rw [LinearMap.convMul_def, ofConv_toConv, ofConv_toConv, ofConv_toConv,
        LinearMap.convOne_def, ofConv_toConv] at h
      exact h }

p2m_export "HopfAlgebra.SecondIso" "hopfAlgebra"

theorem map_antipode (a : A) : f (HopfAlgebra.antipode k a) = antipodeQ f hf (f a) := by

  have h1 : pre f (toConv (antipodeQ f hf)) * uu f = 1 := by
    rw [← pre_id, ← map_mul, antipodeQ_mul_id, map_one]
  have h2 : pre f (toConv (antipodeQ f hf)) = vv f :=
    left_inv_eq_right_inv h1 (uu_mul_vv f)
  have := congrArg (fun e : FQ (k := k) A Q => e.ofConv a) h2
  exact this.symm

end Upgrade

end HopfAlgebra.SecondIso
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker.HopfAlgebra P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker.HopfAlgebra.SecondIso"
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker.HopfAlgebra"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mul_antipode_rTensor_comul mul_antipode_lTensor_comul coaction_apply hopfKer mem_hopfKer_iff IsHopfGalois HopfKerHopf.antipode_mem HopfKerHopf.ι₂_tmul HopfKerHopf.comul_coe_mem_range IsHopfTower mem_augIdeal IsHopfSubalgebra HopfTower.augIdealMap HopfTower.fwdAux HopfTower.fwdAux_algebraMap HopfTower.galoisEquiv HopfTower.galoisEquiv_tmul isHopfGalois_iff_ker_le_span_of_surjective isHopfGalois_of_surjective faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem"
namespace SecondIso
p2m_open "HopfAlgebra"

section Coinv

variable {k : Type u} [Field k]

theorem map_id_injective {X Y Z : Type*} [CommRing X] [CommRing Y] [CommRing Z] [Algebra k X]
    [Algebra k Y] [Algebra k Z] (e : Y →ₐ[k] Z) (he : Injective e) :
    Injective (Algebra.TensorProduct.map (AlgHom.id k X) e) := by
  have h1 : Injective (e.toLinearMap.lTensor X) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ he
  have key : (Algebra.TensorProduct.map (AlgHom.id k X) e).toLinearMap = e.toLinearMap.lTensor X :=
    TensorProduct.ext' fun _ _ => rfl
  have : Injective (Algebra.TensorProduct.map (AlgHom.id k X) e).toLinearMap := by
    rw [key]; exact h1
  exact this

theorem coinv_iff_of_injective {X Y Z : Type*} [CommRing X] [Bialgebra k X] [CommRing Y]
    [CommRing Z] [Algebra k Y] [Algebra k Z] (g : X →ₐ[k] Y) (e : Y →ₐ[k] Z) (he : Injective e)
    (b : X) :
    Algebra.TensorProduct.map (AlgHom.id k X) (e.comp g) (Coalgebra.comul (R := k) b) = b ⊗ₜ[k] 1 ↔
      Algebra.TensorProduct.map (AlgHom.id k X) g (Coalgebra.comul (R := k) b) = b ⊗ₜ[k] 1 := by
  have hcomp : Algebra.TensorProduct.map (AlgHom.id k X) (e.comp g) =
      (Algebra.TensorProduct.map (AlgHom.id k X) e).comp
        (Algebra.TensorProduct.map (AlgHom.id k X) g) := by
    rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp]
  rw [hcomp, AlgHom.comp_apply]
  constructor
  · intro h
    apply map_id_injective e he
    rw [h, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  · intro h
    rw [h, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

theorem mem_hopfKer_iff_mkₐ {X D : Type*} [CommRing X] [Bialgebra k X] [CommRing D] [Bialgebra k D]
    (ρ : X →ₐc[k] D) (b : X) :
    b ∈ HopfAlgebra.hopfKer ρ ↔
      Algebra.TensorProduct.map (AlgHom.id k X) (Ideal.Quotient.mkₐ k (RingHom.ker (ρ : X →ₐ[k] D)))
        (Coalgebra.comul (R := k) b) = b ⊗ₜ[k] 1 := by
  rw [HopfAlgebra.mem_hopfKer_iff, HopfAlgebra.coaction_apply]
  have hfac : (ρ : X →ₐ[k] D) = (Ideal.kerLiftAlg (ρ : X →ₐ[k] D)).comp
      (Ideal.Quotient.mkₐ k (RingHom.ker (ρ : X →ₐ[k] D))) := by
    refine AlgHom.ext fun x => ?_; rfl
  conv_lhs => rw [hfac]
  exact coinv_iff_of_injective _ _ (Ideal.kerLiftAlg_injective _) b

theorem coinv_iff_of_eq {X : Type*} [CommRing X] [Bialgebra k X] {I J : Ideal X} (hIJ : I = J)
    (b : X) :
    Algebra.TensorProduct.map (AlgHom.id k X) (Ideal.Quotient.mkₐ k I) (Coalgebra.comul (R := k) b) =
        b ⊗ₜ[k] 1 ↔
      Algebra.TensorProduct.map (AlgHom.id k X) (Ideal.Quotient.mkₐ k J) (Coalgebra.comul (R := k) b) =
        b ⊗ₜ[k] 1 := by
  subst hIJ; exact Iff.rfl

end Coinv
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker.HopfAlgebra P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker.HopfAlgebra.SecondIso"

section Takeuchi

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H] [Module.Finite k H]
variable (K : Subalgebra k H) (hK : HopfAlgebra.IsHopfSubalgebra k K)

def KplusH : Ideal H := Ideal.span {x | x ∈ K ∧ Coalgebra.counit (R := k) x = 0}

theorem KplusH_eq :
    letI := hK.hopfAlgebra
    KplusH K = HopfTower.augIdealMap k ↥K H := by
  letI := hK.hopfAlgebra
  change Ideal.span _ = Ideal.span _
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, HopfAlgebra.mem_augIdeal]
  constructor
  · rintro ⟨hx, hε⟩
    exact ⟨⟨x, hx⟩, hε, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.2, hs⟩

def coinvSub (J : Ideal H) : Subalgebra k H :=
  AlgHom.equalizer
    ((Algebra.TensorProduct.map (AlgHom.id k H) (Ideal.Quotient.mkₐ k J)).comp
      (Bialgebra.comulAlgHom k H))
    (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] (H ⧸ J))

theorem mem_coinvSub_iff (J : Ideal H) (b : H) :
    b ∈ coinvSub (k := k) J ↔
      Algebra.TensorProduct.map (AlgHom.id k H) (Ideal.Quotient.mkₐ k J) (Coalgebra.comul (R := k) b) =
        b ⊗ₜ[k] 1 := Iff.rfl

include hK in

theorem mem_of_coinv (b : H)
    (hb : Algebra.TensorProduct.map (AlgHom.id k H) (Ideal.Quotient.mkₐ k (KplusH K))
      (Coalgebra.comul (R := k) b) = b ⊗ₜ[k] 1) : b ∈ K := by
  letI hKH : HopfAlgebra k ↥K := hK.hopfAlgebra
  haveI hT : HopfAlgebra.IsHopfTower k ↥K H := hK.isHopfTower
  haveI hff : Module.FaithfullyFlat ↥K H :=
    HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem K hK.comul_mem
      hK.antipode_mem
  set J : Ideal H := HopfTower.augIdealMap k ↥K H with hJ
  have hIJ : KplusH K = J := KplusH_eq K hK
  rw [coinv_iff_of_eq hIJ] at hb
  have fwdAux_eq : ∀ b : H, HopfTower.fwdAux k ↥K H H b =
      Algebra.TensorProduct.map (AlgHom.id k H) (Ideal.Quotient.mkₐ k J)
        (Coalgebra.comul (R := k) b) := fun b => by
    change Algebra.TensorProduct.map (IsScalarTower.toAlgHom k H H) (Ideal.Quotient.mkₐ k J)
      (Coalgebra.comul (R := k) b) = _
    congr 1

  set K' : Subalgebra k H := coinvSub (k := k) J with hK'
  have hbK' : b ∈ K' := hb
  have hle : K ≤ K' := fun s hs => by
    change s ∈ coinvSub (k := k) J
    rw [mem_coinvSub_iff, ← fwdAux_eq]
    exact HopfTower.fwdAux_algebraMap k ↥K H H ⟨s, hs⟩

  letI algKK' : Algebra ↥K ↥K' := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  have halg : ∀ s : ↥K, ((algebraMap ↥K ↥K' s : ↥K') : H) = (s : H) := fun s => rfl

  have hsurj : Surjective (algebraMap H (H ⊗[↥K] ↥K')) := by
    let incl : ↥K' →ₗ[↥K] H :=
      { toFun := fun x => (x : H)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let lT : H ⊗[↥K] ↥K' →ₗ[↥K] H ⊗[↥K] H := incl.lTensor H
    have hlT : Injective lT :=
      Module.Flat.lTensor_preserves_injective_linearMap incl (fun x y h => Subtype.ext h)
    let m : H ⊗[↥K] ↥K' →ₗ[↥K] H := LinearMap.mul' ↥K H ∘ₗ lT
    have key : ∀ z, lT z = m z ⊗ₜ[↥K] (1 : H) := by
      intro z
      induction z with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy, TensorProduct.add_tmul]
      | tmul h x =>
        change h ⊗ₜ[↥K] (x : H) = (h * (x : H)) ⊗ₜ[↥K] (1 : H)
        apply (HopfTower.galoisEquiv k ↥K H H).injective
        rw [HopfTower.galoisEquiv_tmul, HopfTower.galoisEquiv_tmul, map_one, mul_one, fwdAux_eq]
        have hx : Algebra.TensorProduct.map (AlgHom.id k H) (Ideal.Quotient.mkₐ k J)
            (Coalgebra.comul (R := k) (x : H)) = (x : H) ⊗ₜ[k] 1 := x.2
        rw [hx, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    intro z
    refine ⟨m z, ?_⟩
    apply hlT
    rw [key z, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    change (m z) ⊗ₜ[↥K] ((1 : ↥K') : H) = _
    rw [OneMemClass.coe_one]
  have hdesc := Module.FaithfullyFlat.surjective_of_tensorProduct (R := ↥K) (S := H) (T := ↥K') hsurj
  obtain ⟨s, hs⟩ := hdesc ⟨b, hbK'⟩
  have : (s : H) = b := by rw [← halg s, hs]
  rw [← this]; exact s.2

end Takeuchi
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker.HopfAlgebra P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker.HopfAlgebra.SecondIso"

end HopfAlgebra.SecondIso
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker.HopfAlgebra P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker.HopfAlgebra.SecondIso"
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker.HopfAlgebra P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker.HopfAlgebra.SecondIso"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mul_antipode_rTensor_comul mul_antipode_lTensor_comul coaction_apply hopfKer mem_hopfKer_iff IsHopfGalois HopfKerHopf.antipode_mem HopfKerHopf.ι₂_tmul HopfKerHopf.comul_coe_mem_range IsHopfTower mem_augIdeal IsHopfSubalgebra HopfTower.augIdealMap HopfTower.fwdAux HopfTower.fwdAux_algebraMap HopfTower.galoisEquiv HopfTower.galoisEquiv_tmul isHopfGalois_iff_ker_le_span_of_surjective isHopfGalois_of_surjective faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem"
namespace SecondIso
p2m_open "HopfAlgebra"

section Assembly

variable (k : Type u) [Field k]
variable {A : Type v} [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
variable {B : Type w} [CommRing B] [Bialgebra k B]
variable {C : Type x} [CommRing C] [Bialgebra k C]
variable {D : Type y} [CommRing D] [Bialgebra k D]
variable (π : A →ₐc[k] B) (μ : A →ₐc[k] C) (ρ : B →ₐc[k] D)
variable (hπ : Surjective π) (hμ : Surjective μ) (hρ : Surjective ρ)
variable (hker : RingHom.ker (ρ : B →ₐ[k] D) =
  Ideal.map (π : A →ₐ[k] B) (RingHom.ker (μ : A →ₐ[k] C)))

theorem apply_eq_zero_of_mem_hopfKer {a : A} (ha : a ∈ HopfAlgebra.hopfKer μ)
    (hε : Coalgebra.counit (R := k) a = 0) : μ a = 0 := by
  have hco : Algebra.TensorProduct.map (AlgHom.id k A) (μ : A →ₐ[k] C)
      (Coalgebra.comul (R := k) a) = a ⊗ₜ[k] 1 := ha

  let L : A ⊗[k] C →ₗ[k] C := TensorProduct.lift
    ((LinearMap.lsmul k C).comp (Coalgebra.counit (R := k) (A := A)))
  have hL : ∀ z : A ⊗[k] A, L (Algebra.TensorProduct.map (AlgHom.id k A) (μ : A →ₐ[k] C) z) =
      (μ : A →ₐ[k] C).toLinearMap (TensorProduct.lift ((LinearMap.lsmul k A).comp
        (Coalgebra.counit (R := k) (A := A))) z) := by
    intro z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => simp [L]
  have h1 := congrArg L hco
  rw [hL] at h1
  have h2 : TensorProduct.lift ((LinearMap.lsmul k A).comp (Coalgebra.counit (R := k) (A := A)))
      (Coalgebra.comul (R := k) a) = a := by
    have := Coalgebra.rTensor_counit_comul (R := k) a
    have h3 : TensorProduct.lift ((LinearMap.lsmul k A).comp (Coalgebra.counit (R := k) (A := A))) =
        (TensorProduct.lid k A).toLinearMap ∘ₗ (Coalgebra.counit (R := k) (A := A)).rTensor A :=
      TensorProduct.ext' fun x y => by simp
    rw [h3, LinearMap.comp_apply, this]; simp
  rw [h2] at h1
  simp only [L, TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.lsmul_apply, hε,
    zero_smul, AlgHom.toLinearMap_apply] at h1
  exact h1

include hπ hμ hρ hker in

theorem map_hopfKer_eq : (HopfAlgebra.hopfKer μ).map (π : A →ₐ[k] B) = HopfAlgebra.hopfKer ρ := by
  haveI : Module.Finite k B := Module.Finite.of_surjective (π : A →ₐ[k] B).toLinearMap hπ
  haveI : Module.Finite k C := Module.Finite.of_surjective (μ : A →ₐ[k] C).toLinearMap hμ
  letI hB : HopfAlgebra k B := hopfAlgebra π hπ
  letI hC : HopfAlgebra k C := hopfAlgebra μ hμ
  set A' : Subalgebra k A := HopfAlgebra.hopfKer μ with hA'
  set K : Subalgebra k B := A'.map (π : A →ₐ[k] B) with hKdef

  have hle1 : K ≤ HopfAlgebra.hopfKer ρ := by
    rintro x ⟨a, ha, rfl⟩
    have hkk : RingHom.ker (μ : A →ₐ[k] C).toRingHom ≤
        RingHom.ker ((ρ : B →ₐ[k] D).comp (π : A →ₐ[k] B)).toRingHom := by
      intro z hz
      have hz' : (π : A →ₐ[k] B) z ∈ RingHom.ker (ρ : B →ₐ[k] D) := by
        rw [hker]; exact Ideal.mem_map_of_mem _ hz
      exact hz'
    let θ : C →ₐ[k] D := AlgHom.liftOfSurjective (μ : A →ₐ[k] C) hμ
      ((ρ : B →ₐ[k] D).comp (π : A →ₐ[k] B)) hkk
    have hθ : (ρ : B →ₐ[k] D).comp (π : A →ₐ[k] B) = θ.comp (μ : A →ₐ[k] C) :=
      (AlgHom.liftOfSurjective_comp _ hμ _ hkk).symm
    have hΔ := AlgHom.congr_fun (BialgHom.map_comp_comulAlgHom π) a
    simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply] at hΔ
    change Algebra.TensorProduct.map (AlgHom.id k B) (ρ : B →ₐ[k] D)
      (Coalgebra.comul (R := k) ((π : A →ₐ[k] B) a)) = (π : A →ₐ[k] B) a ⊗ₜ[k] 1
    rw [← hΔ, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp, hθ,
      ← AlgHom.comp_id (π : A →ₐ[k] B), Algebra.TensorProduct.map_comp, AlgHom.comp_apply,
      AlgHom.comp_id]
    have hco : Algebra.TensorProduct.map (AlgHom.id k A) (μ : A →ₐ[k] C)
        (Coalgebra.comul (R := k) a) = a ⊗ₜ[k] 1 := ha
    rw [hco, Algebra.TensorProduct.map_tmul, map_one]

  have hK : HopfAlgebra.IsHopfSubalgebra k K := by
    refine ⟨?_, ?_⟩
    · rintro x ⟨a, ha, rfl⟩
      obtain ⟨z, hz⟩ := HopfKerHopf.comul_coe_mem_range μ ⟨a, ha⟩
      have hΔ := AlgHom.congr_fun (BialgHom.map_comp_comulAlgHom π) a
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply] at hΔ
      change Coalgebra.comul (R := k) ((π : A →ₐ[k] B) a) ∈ _
      rw [← hΔ]
      change Algebra.TensorProduct.map (π : A →ₐ[k] B) (π : A →ₐ[k] B)
        (Coalgebra.comul (R := k) ((⟨a, ha⟩ : ↥A') : A)) ∈ _
      rw [← hz]
      clear hz
      induction z with
      | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
      | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
      | tmul s t =>
        rw [HopfKerHopf.ι₂_tmul, Algebra.TensorProduct.map_tmul]
        exact Submodule.subset_span ⟨π s, ⟨s, s.2, rfl⟩, π t, ⟨t, t.2, rfl⟩, rfl⟩
    · rintro x ⟨a, ha, rfl⟩
      refine ⟨HopfAlgebra.antipode k a, HopfKerHopf.antipode_mem μ ha, ?_⟩
      exact map_antipode π hπ a

  have hG : HopfAlgebra.IsHopfGalois μ := HopfAlgebra.isHopfGalois_of_surjective μ hμ
  have hNC : RingHom.ker (μ : A →ₐ[k] C) =
      Ideal.span {a | a ∈ A' ∧ Coalgebra.counit (R := k) a = 0} := by
    apply le_antisymm ((HopfAlgebra.isHopfGalois_iff_ker_le_span_of_surjective μ hμ).1 hG)
    rw [Ideal.span_le]
    rintro a ⟨ha, hε⟩
    exact apply_eq_zero_of_mem_hopfKer k μ ha hε
  have hKplus : KplusH K = RingHom.ker (ρ : B →ₐ[k] D) := by
    rw [hker, hNC, Ideal.map_span, KplusH]
    congr 1
    ext x
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hε⟩
      refine ⟨a, ⟨ha, ?_⟩, rfl⟩
      have : Coalgebra.counit (R := k) (π a) = Coalgebra.counit (R := k) a :=
        CoalgHomClass.counit_comp_apply π a
      rw [← this]; exact hε
    · rintro ⟨a, ⟨ha, hε⟩, rfl⟩
      refine ⟨⟨a, ha, rfl⟩, ?_⟩
      change Coalgebra.counit (R := k) (π a) = 0
      rw [CoalgHomClass.counit_comp_apply π a]; exact hε

  refine le_antisymm hle1 fun b hb => ?_
  have hb1 := (mem_hopfKer_iff_mkₐ ρ b).1 hb
  rw [← coinv_iff_of_eq hKplus] at hb1
  exact mem_of_coinv K hK b hb1

end Assembly
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker.HopfAlgebra P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker.HopfAlgebra.SecondIso"

end HopfAlgebra.SecondIso
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker.HopfAlgebra P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker.HopfAlgebra.SecondIso"
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker.HopfAlgebra P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker.HopfAlgebra.SecondIso"

theorem solution
    (k : Type u) [Field k]
    {A : Type v} [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    {B : Type w} [CommRing B] [Bialgebra k B]
    {C : Type x} [CommRing C] [Bialgebra k C]
    {D : Type y} [CommRing D] [Bialgebra k D]
    (π : A →ₐc[k] B) (μ : A →ₐc[k] C) (ρ : B →ₐc[k] D)
    (hπ : Function.Surjective π) (hμ : Function.Surjective μ) (hρ : Function.Surjective ρ)
    (hker : RingHom.ker (ρ : B →ₐ[k] D) =
      Ideal.map (π : A →ₐ[k] B) (RingHom.ker (μ : A →ₐ[k] C))) :
    (HopfAlgebra.hopfKer μ).map (π : A →ₐ[k] B) = HopfAlgebra.hopfKer ρ :=
  HopfAlgebra.SecondIso.map_hopfKer_eq k π μ ρ hπ hμ hρ hker

end
end S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker
end P2MW
export P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker (solution)
