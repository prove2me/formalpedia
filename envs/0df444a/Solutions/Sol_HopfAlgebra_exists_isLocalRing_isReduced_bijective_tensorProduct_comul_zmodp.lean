-- Prove2me | solution 1 for HopfAlgebra.exists_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4fb0d930-4cb5-51de-bfd7-21668b6cbf30

import Mathlib
import Definitions.Def_HopfAlgebra_HopfIdealQuotient
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_HopfAlgebra_exists_isReduced_bialgHom_injective_comp_eq_pow_zmodp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp

set_option autoImplicit false

universe u v w

open scoped TensorProduct
open Coalgebra Bialgebra WithConv

noncomputable section

namespace ConnectedEtaleSplitting

section General

variable {R : Type u} [CommRing R]
variable {B : Type v} [CommRing B] [HopfAlgebra R B]
variable {H : Type w} [CommRing H] [HopfAlgebra R H]

def Jideal (σ : H →ₐc[R] B) : Ideal B :=
  Ideal.map (σ : H →ₐ[R] B) (RingHom.ker (counitAlgHom R H))

theorem σ_mem_J (σ : H →ₐc[R] B) {y : H} (hy : counit (R := R) y = 0) : σ y ∈ Jideal σ :=
  Ideal.mem_map_of_mem _ (by simpa [RingHom.mem_ker] using hy)

theorem σ_sub_algebraMap_mem_J (σ : H →ₐc[R] B) (y : H) :
    σ y - algebraMap R B (counit (R := R) y) ∈ Jideal σ := by
  have h : σ (y - algebraMap R H (counit (R := R) y)) ∈ Jideal σ :=
    σ_mem_J σ (by simp)
  have hc : σ (algebraMap R H (counit (R := R) y)) = algebraMap R B (counit (R := R) y) :=
    AlgHomClass.commutes σ _
  rwa [map_sub, hc] at h

theorem J_le_ker_counit (σ : H →ₐc[R] B) : Jideal σ ≤ RingHom.ker (counitAlgHom R B) := by
  rw [Jideal, Ideal.map_le_iff_le_comap]
  intro y hy
  rw [Ideal.mem_comap, RingHom.mem_ker, Bialgebra.counitAlgHom_apply]
  rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at hy
  change counit (R := R) ((σ : H →ₐc[R] B) y) = 0
  rw [CoalgHomClass.counit_comp_apply, hy]

theorem antipodeAlgHom_comp_eq (f : H →ₐc[R] B) :
    (HopfAlgebra.antipodeAlgHom R B).comp (f : H →ₐ[R] B) =
      (f : H →ₐ[R] B).comp (HopfAlgebra.antipodeAlgHom R H) := by
  refine AlgHom.ext fun y => ?_
  simp only [AlgHom.comp_apply, HopfAlgebra.antipodeAlgHom_apply]
  exact (HopfAlgebra.HopfKerHopf.map_antipode f y).symm

theorem antipode_mem_J (σ : H →ₐc[R] B) {x : B} (hx : x ∈ Jideal σ) :
    HopfAlgebra.antipode R x ∈ Jideal σ := by
  have h1 : Jideal σ ≤ Ideal.comap (HopfAlgebra.antipodeAlgHom R B) (Jideal σ) := by
    refine Ideal.map_le_iff_le_comap.2 fun y hy => ?_
    rw [Ideal.mem_comap, Ideal.mem_comap, HopfAlgebra.antipodeAlgHom_apply, BialgHom.coe_toAlgHom,
      ← HopfAlgebra.HopfKerHopf.map_antipode σ y]
    refine σ_mem_J σ ?_
    rw [HopfAlgebra.counit_antipode]
    simpa [RingHom.mem_ker] using hy
  have := h1 hx
  rwa [Ideal.mem_comap, HopfAlgebra.antipodeAlgHom_apply] at this

def unitCounit (C : Type*) [CommRing C] [Algebra R C] : H →ₐ[R] C :=
  (Algebra.ofId R C).comp (counitAlgHom R H)

@[scoped simp] theorem unitCounit_apply (C : Type*) [CommRing C] [Algebra R C] (y : H) :
    unitCounit (R := R) (H := H) C y = algebraMap R C (counit (R := R) y) := rfl

theorem map_unitCounit_comul {C D : Type*} [CommRing C] [Algebra R C] [CommRing D] [Algebra R D]
    (g : H →ₐ[R] D) (y : H) :
    Algebra.TensorProduct.map (unitCounit (R := R) (H := H) C) g (comul (R := R) y) =
      (1 : C) ⊗ₜ[R] g y := by
  have hrepr := (ℛ R y).eq
  rw [← hrepr, map_sum]
  simp only [Algebra.TensorProduct.map_tmul, unitCounit_apply]
  have h2 : ∀ i ∈ (ℛ R y).index,
      algebraMap R C (counit (R := R) ((ℛ R y).left i)) ⊗ₜ[R] g ((ℛ R y).right i) =
        (1 : C) ⊗ₜ[R] g (counit (R := R) ((ℛ R y).left i) • (ℛ R y).right i) := by
    intro i _
    rw [map_smul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [Finset.sum_congr rfl h2, ← TensorProduct.tmul_sum, ← map_sum, Coalgebra.sum_counit_smul]

theorem map_unitCounit_unitCounit_comul {C D : Type*} [CommRing C] [Algebra R C] [CommRing D]
    [Algebra R D] (y : H) :
    Algebra.TensorProduct.map (unitCounit (R := R) (H := H) C) (unitCounit (R := R) (H := H) D)
        (comul (R := R) y) = algebraMap R (C ⊗[R] D) (counit (R := R) y) := by
  rw [map_unitCounit_comul, unitCounit_apply, Algebra.TensorProduct.algebraMap_apply']

theorem mkₐ_comp_σ (σ : H →ₐc[R] B) :
    (Ideal.Quotient.mkₐ R (Jideal σ)).comp (σ : H →ₐ[R] B) =
      unitCounit (R := R) (H := H) (B ⧸ Jideal σ) := by
  refine AlgHom.ext fun y => ?_
  rw [AlgHom.comp_apply, unitCounit_apply, Ideal.Quotient.mkₐ_eq_mk,
    IsScalarTower.algebraMap_apply R B (B ⧸ Jideal σ), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq]
  exact σ_sub_algebraMap_mem_J σ y

theorem map_comul_map {C D : Type*} [CommRing C] [Algebra R C] [CommRing D] [Algebra R D]
    (f : B →ₐ[R] C) (g : B →ₐ[R] D) (σ : H →ₐc[R] B) (y : H) :
    Algebra.TensorProduct.map f g (comul (R := R) ((σ : H →ₐc[R] B) y)) =
      Algebra.TensorProduct.map (f.comp (σ : H →ₐ[R] B)) (g.comp (σ : H →ₐ[R] B))
        (comul (R := R) y) := by
  rw [← CoalgHomClass.map_comp_comul_apply]
  generalize comul (R := R) y = z
  induction z with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem isHopfIdeal_J (σ : H →ₐc[R] B) : (Jideal σ).IsHopfIdeal' R := by
  refine ⟨?_, ?_, ?_⟩
  ·
    intro x hx
    let F : B →ₐ[R] (B ⧸ Jideal σ) ⊗[R] (B ⧸ Jideal σ) :=
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Jideal σ))
        (Ideal.Quotient.mkₐ R (Jideal σ))).comp (comulAlgHom R B)
    have hle : Jideal σ ≤ RingHom.ker F := by
      refine Ideal.map_le_iff_le_comap.2 fun y hy => ?_
      rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at hy
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Jideal σ))
        (Ideal.Quotient.mkₐ R (Jideal σ))) (comul (R := R) (σ y)) = 0
      rw [map_comul_map, mkₐ_comp_σ, map_unitCounit_unitCounit_comul, hy, map_zero]
    have := hle hx
    rwa [RingHom.mem_ker] at this
  · intro x hx
    have := J_le_ker_counit σ hx
    rwa [RingHom.mem_ker] at this
  · intro x hx
    exact antipode_mem_J σ hx

attribute [local instance] isHopfIdeal_J

abbrev qc (σ : H →ₐc[R] B) : B →ₐc[R] B ⧸ Jideal σ := HopfAlgebra.quotientBialgHom R (Jideal σ)

theorem qc_apply (σ : H →ₐc[R] B) (b : B) : qc σ b = Ideal.Quotient.mk (Jideal σ) b := rfl

theorem qc_toAlgHom (σ : H →ₐc[R] B) :
    (qc σ : B →ₐ[R] B ⧸ Jideal σ) = Ideal.Quotient.mkₐ R (Jideal σ) := rfl

theorem qc_surjective (σ : H →ₐc[R] B) : Function.Surjective (qc σ) := Ideal.Quotient.mk_surjective

theorem ker_qc (σ : H →ₐc[R] B) : RingHom.ker (qc σ : B →ₐ[R] B ⧸ Jideal σ) = Jideal σ := by
  rw [qc_toAlgHom]
  exact Ideal.Quotient.mkₐ_ker R (Jideal σ)

theorem qc_comp_σ (σ : H →ₐc[R] B) :
    (qc σ : B →ₐ[R] B ⧸ Jideal σ).comp (σ : H →ₐ[R] B) =
      unitCounit (R := R) (H := H) (B ⧸ Jideal σ) := by
  rw [qc_toAlgHom]; exact mkₐ_comp_σ σ

def inclL (σ : H →ₐc[R] B) : (B ⧸ Jideal σ) →ₐ[R] (B ⧸ Jideal σ) ⊗[R] H :=
  Algebra.TensorProduct.includeLeft

def inclR (σ : H →ₐc[R] B) : H →ₐ[R] (B ⧸ Jideal σ) ⊗[R] H :=
  Algebra.TensorProduct.includeRight

@[scoped simp] theorem inclL_apply (σ : H →ₐc[R] B) (x : B ⧸ Jideal σ) : inclL σ x = x ⊗ₜ[R] (1 : H) := rfl

@[scoped simp] theorem inclR_apply (σ : H →ₐc[R] B) (y : H) : inclR σ y = (1 : B ⧸ Jideal σ) ⊗ₜ[R] y := rfl

def ThetaAlg (πe : B →ₐc[R] H) (σ : H →ₐc[R] B) : B →ₐ[R] (B ⧸ Jideal σ) ⊗[R] H :=
  (Algebra.TensorProduct.map (qc σ : B →ₐ[R] B ⧸ Jideal σ) (πe : B →ₐ[R] H)).comp (comulAlgHom R B)

theorem ThetaAlg_apply (πe : B →ₐc[R] H) (σ : H →ₐc[R] B) (b : B) :
    ThetaAlg πe σ b = Algebra.TensorProduct.map (qc σ : B →ₐ[R] B ⧸ Jideal σ) (πe : B →ₐ[R] H)
      (comul (R := R) b) := rfl

theorem ThetaAlg_eq_convMul (πe : B →ₐc[R] H) (σ : H →ₐc[R] B) :
    ThetaAlg πe σ =
      (toConv ((inclL σ).comp (qc σ : B →ₐ[R] B ⧸ Jideal σ)) *
        toConv ((inclR σ).comp (πe : B →ₐ[R] H))).ofConv := by
  rw [AlgHom.convMul_def, ofConv_toConv, ofConv_toConv, ← AlgHom.comp_assoc,
    Algebra.TensorProduct.lmul'_comp_map, ThetaAlg]
  congr 1
  refine Algebra.TensorProduct.ext' fun a b => ?_
  simp [Algebra.TensorProduct.lift_tmul, inclL, inclR]

def gMap (πe : B →ₐc[R] H) (σ : H →ₐc[R] B) : B →ₐ[R] B :=
  (σ : H →ₐ[R] B).comp (πe : B →ₐ[R] H)

theorem gMap_apply (πe : B →ₐc[R] H) (σ : H →ₐc[R] B) (b : B) : gMap πe σ b = σ (πe b) := rfl

def phiMap (πe : B →ₐc[R] H) (σ : H →ₐc[R] B) : B →ₐ[R] B :=
  (toConv (AlgHom.id R B) * toConv ((gMap πe σ).comp (HopfAlgebra.antipodeAlgHom R B))).ofConv

theorem comp_phiMap_eq {T : Type*} [CommSemiring T] [Algebra R T] (πe : B →ₐc[R] H)
    (σ : H →ₐc[R] B) (h : B →ₐ[R] T) :
    h.comp (phiMap πe σ) =
      (toConv h * toConv (h.comp ((gMap πe σ).comp (HopfAlgebra.antipodeAlgHom R B)))).ofConv := by
  rw [phiMap, AlgHom.comp_convMul_distrib]
  simp only [AlgHom.comp_id]

theorem conv_cancel_right {T : Type*} [CommSemiring T] [Algebra R T] (θ x y : B →ₐ[R] T)
    (hθ : θ = (toConv x * toConv y).ofConv) :
    (toConv θ * toConv (y.comp (HopfAlgebra.antipodeAlgHom R B))).ofConv = x := by
  rw [hθ, toConv_ofConv, mul_assoc, HopfAlgebra.convMul_comp_antipodeAlgHom, mul_one, ofConv_toConv]

section WithSection

variable (πe : B →ₐc[R] H) (σ : H →ₐc[R] B) (hsec : πe.comp σ = BialgHom.id R H)
include hsec

theorem πe_σ (y : H) : πe (σ y) = y := by
  have := DFunLike.congr_fun hsec y
  simpa using this

theorem πe_σ' (y : H) : (πe : B →ₐ[R] H) ((σ : H →ₐ[R] B) y) = y := by
  rw [BialgHom.coe_toAlgHom, BialgHom.coe_toAlgHom, πe_σ πe σ hsec]

theorem phiMap_comp_σ : (phiMap πe σ).comp (σ : H →ₐ[R] B) = unitCounit (R := R) (H := H) B := by
  rw [phiMap, AlgHom.convMul_comp_bialgHom_distrib, ofConv_toConv, ofConv_toConv, AlgHom.id_comp]
  have h1 : ((gMap πe σ).comp (HopfAlgebra.antipodeAlgHom R B)).comp (σ : H →ₐ[R] B) =
      (σ : H →ₐ[R] B).comp (HopfAlgebra.antipodeAlgHom R H) := by
    rw [AlgHom.comp_assoc, antipodeAlgHom_comp_eq, ← AlgHom.comp_assoc]
    congr 1
    refine AlgHom.ext fun y => ?_
    simp only [AlgHom.comp_apply, gMap_apply, BialgHom.coe_toAlgHom, πe_σ πe σ hsec]
  rw [h1, HopfAlgebra.convMul_comp_antipodeAlgHom, AlgHom.convOne_def, ofConv_toConv]
  rfl

theorem phiMap_σ (y : H) : phiMap πe σ (σ y) = algebraMap R B (counit (R := R) y) := by
  have := AlgHom.congr_fun (phiMap_comp_σ πe σ hsec) y
  simpa using this

theorem phiMap_mem_J {x : B} (hx : x ∈ Jideal σ) : phiMap πe σ x = 0 := by
  have hle : Jideal σ ≤ RingHom.ker (phiMap πe σ) := by
    refine Ideal.map_le_iff_le_comap.2 fun y hy => ?_
    rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at hy
    rw [Ideal.mem_comap, RingHom.mem_ker, BialgHom.coe_toAlgHom, phiMap_σ πe σ hsec, hy, map_zero]
  exact hle hx

def phiBar : B ⧸ Jideal σ →ₐ[R] B :=
  HopfAlgebra.quotientLiftPoint R (Jideal σ) (phiMap πe σ) (fun _ hx => phiMap_mem_J πe σ hsec hx)

theorem phiBar_comp_qc :
    (phiBar πe σ hsec).comp (qc σ : B →ₐ[R] B ⧸ Jideal σ) = phiMap πe σ :=
  HopfAlgebra.quotientLiftPoint_comp_mkₐ R (Jideal σ) _ _

def PsiMap : (B ⧸ Jideal σ) ⊗[R] H →ₐ[R] B :=
  Algebra.TensorProduct.lift (phiBar πe σ hsec) (σ : H →ₐ[R] B) (fun _ _ => .all _ _)

theorem PsiMap_comp_ThetaAlg : (PsiMap πe σ hsec).comp (ThetaAlg πe σ) = AlgHom.id R B := by
  rw [ThetaAlg, ← AlgHom.comp_assoc]
  have h1 : (PsiMap πe σ hsec).comp
      (Algebra.TensorProduct.map (qc σ : B →ₐ[R] B ⧸ Jideal σ) (πe : B →ₐ[R] H)) =
      Algebra.TensorProduct.lift (phiMap πe σ) (gMap πe σ) (fun _ _ => .all _ _) := by
    refine Algebra.TensorProduct.ext' fun a b => ?_
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, PsiMap,
      Algebra.TensorProduct.lift_tmul]
    rw [← phiBar_comp_qc πe σ hsec]
    rfl
  rw [h1, ← Algebra.TensorProduct.lmul'_comp_map]
  have h2 : (Algebra.TensorProduct.lmul' R (S := B)).comp
      ((Algebra.TensorProduct.map (phiMap πe σ) (gMap πe σ)).comp (comulAlgHom R B)) =
      (toConv (phiMap πe σ) * toConv (gMap πe σ)).ofConv := by
    rw [AlgHom.convMul_def]
  rw [AlgHom.comp_assoc, h2, phiMap, toConv_ofConv, mul_assoc,
    HopfAlgebra.comp_antipodeAlgHom_convMul, mul_one, ofConv_toConv]

theorem ThetaAlg_comp_σ : (ThetaAlg πe σ).comp (σ : H →ₐ[R] B) = inclR σ := by
  refine AlgHom.ext fun y => ?_
  rw [AlgHom.comp_apply, ThetaAlg_apply, BialgHom.coe_toAlgHom,
    map_comul_map, qc_comp_σ, map_unitCounit_comul, inclR_apply,
    AlgHom.comp_apply, πe_σ' πe σ hsec]

theorem ThetaAlg_comp_phiMap :
    (ThetaAlg πe σ).comp (phiMap πe σ) = (inclL σ).comp (qc σ : B →ₐ[R] B ⧸ Jideal σ) := by
  rw [comp_phiMap_eq]
  have h1 : (ThetaAlg πe σ).comp ((gMap πe σ).comp (HopfAlgebra.antipodeAlgHom R B)) =
      ((inclR σ).comp (πe : B →ₐ[R] H)).comp (HopfAlgebra.antipodeAlgHom R B) := by
    rw [← AlgHom.comp_assoc, gMap, ← AlgHom.comp_assoc, ThetaAlg_comp_σ πe σ hsec]
  rw [h1]
  exact conv_cancel_right _ _ _ (ThetaAlg_eq_convMul πe σ)

theorem ThetaAlg_comp_PsiMap :
    (ThetaAlg πe σ).comp (PsiMap πe σ hsec) = AlgHom.id R ((B ⧸ Jideal σ) ⊗[R] H) := by
  refine Algebra.TensorProduct.ext ?_ ?_
  ·
    rw [AlgHom.comp_assoc, AlgHom.id_comp]
    have hl : (PsiMap πe σ hsec).comp
        (Algebra.TensorProduct.includeLeft : (B ⧸ Jideal σ) →ₐ[R] (B ⧸ Jideal σ) ⊗[R] H) =
        phiBar πe σ hsec := by
      refine AlgHom.ext fun x => ?_
      simp [PsiMap]
    rw [hl]
    refine Ideal.Quotient.algHom_ext R ?_
    rw [AlgHom.comp_assoc, ← qc_toAlgHom, phiBar_comp_qc πe σ hsec, ThetaAlg_comp_phiMap πe σ hsec]
    rfl
  · refine AlgHom.ext fun y => ?_
    change ThetaAlg πe σ (PsiMap πe σ hsec ((1 : B ⧸ Jideal σ) ⊗ₜ[R] y)) = (1 : B ⧸ Jideal σ) ⊗ₜ[R] y
    rw [PsiMap, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    have := AlgHom.congr_fun (ThetaAlg_comp_σ πe σ hsec) y
    rwa [AlgHom.comp_apply, inclR_apply] at this

theorem ThetaAlg_bijective : Function.Bijective (ThetaAlg πe σ) := by
  have hleft : Function.LeftInverse (PsiMap πe σ hsec) (ThetaAlg πe σ) := fun b => by
    have := AlgHom.congr_fun (PsiMap_comp_ThetaAlg πe σ hsec) b
    simpa using this
  have hright : Function.RightInverse (PsiMap πe σ hsec) (ThetaAlg πe σ) := fun z => by
    have := AlgHom.congr_fun (ThetaAlg_comp_PsiMap πe σ hsec) z
    simpa using this
  exact ⟨hleft.injective, hright.surjective⟩

end WithSection

variable [Coalgebra.IsCocomm R B]

def ThetaMap (πe : B →ₐc[R] H) (σ : H →ₐc[R] B) : B →ₐc[R] (B ⧸ Jideal σ) ⊗[R] H :=
  (Bialgebra.TensorProduct.map (qc σ) πe).comp (Bialgebra.comulBialgHom R B)

theorem ThetaMap_apply (πe : B →ₐc[R] H) (σ : H →ₐc[R] B) (b : B) :
    ThetaMap πe σ b = Algebra.TensorProduct.map (qc σ : B →ₐ[R] B ⧸ Jideal σ) (πe : B →ₐ[R] H)
      (comul (R := R) b) := rfl

theorem coe_ThetaMap (πe : B →ₐc[R] H) (σ : H →ₐc[R] B) :
    (ThetaMap πe σ : B → (B ⧸ Jideal σ) ⊗[R] H) = ThetaAlg πe σ := rfl

theorem ThetaMap_bijective (πe : B →ₐc[R] H) (σ : H →ₐc[R] B)
    (hsec : πe.comp σ = BialgHom.id R H) : Function.Bijective (ThetaMap πe σ) := by
  rw [coe_ThetaMap]
  exact ThetaAlg_bijective πe σ hsec

end General

section PrimeField

variable {p : ℕ} [Fact p.Prime]
variable {B : Type v} [CommRing B] [HopfAlgebra (ZMod p) B]

theorem formallyUnramified_of_isReduced {H : Type v} [CommRing H] [Algebra (ZMod p) H]
    [Module.Finite (ZMod p) H] (hred : IsReduced H) :
    Algebra.FormallyUnramified (ZMod p) H := by
  classical
  haveI : FiniteDimensional (ZMod p) H := ‹Module.Finite (ZMod p) H›
  refine ⟨?_⟩
  by_cases hH : Subsingleton H
  · exact Module.subsingleton H _
  haveI : Nontrivial H := not_subsingleton_iff_nontrivial.mp hH
  haveI : CharP H p := charP_of_injective_algebraMap (algebraMap (ZMod p) H).injective p

  let F : H →ₗ[ZMod p] H :=
    { toFun := fun z => z ^ p
      map_add' := fun a b => add_pow_char a b p
      map_smul' := fun c z => by
        simp only [RingHom.id_apply, Algebra.smul_def, mul_pow, ← map_pow, ZMod.pow_card] }
  have hFinj : Function.Injective F := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    exact hred.eq_zero z ⟨p, hz⟩
  have hFsurj : Function.Surjective F := LinearMap.injective_iff_surjective.1 hFinj
  have hD : ∀ y : H, KaehlerDifferential.D (ZMod p) H y = 0 := fun y => by
    obtain ⟨z, rfl⟩ := hFsurj y
    change KaehlerDifferential.D (ZMod p) H (z ^ p) = 0
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul H, CharP.cast_eq_zero, zero_smul]
  have hspan := KaehlerDifferential.span_range_derivation (R := ZMod p) (S := H)
  have hle : Submodule.span H (Set.range (KaehlerDifferential.D (ZMod p) H)) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    simp [hD y]
  rw [hspan, top_le_iff] at hle
  exact subsingleton_of_forall_eq 0 fun x => by
    have hx : x ∈ (⊤ : Submodule H (Ω[H⁄ZMod p])) := Submodule.mem_top
    rw [← hle] at hx
    exact (Submodule.mem_bot H).1 hx

variable {H : Type v} [CommRing H] [HopfAlgebra (ZMod p) H] [Module.Finite (ZMod p) H]

omit [Module.Finite (ZMod p) H] in

theorem θ_apply_eq_pow (πbar : B →ₐc[ZMod p] H) (jbar : H →ₐc[ZMod p] B)
    (hjinj : Function.Injective jbar) (n : ℕ) (hpow : ∀ b : B, jbar (πbar b) = b ^ p ^ n) (y : H) :
    πbar (jbar y) = y ^ p ^ n := by
  apply hjinj
  rw [hpow, map_pow]

theorem θ_bijective (hred : IsReduced H) (πbar : B →ₐc[ZMod p] H) (jbar : H →ₐc[ZMod p] B)
    (hjinj : Function.Injective jbar) (n : ℕ) (hpow : ∀ b : B, jbar (πbar b) = b ^ p ^ n) :
    Function.Bijective (πbar.comp jbar) := by
  have hinj : Function.Injective (πbar.comp jbar) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    rw [BialgHom.comp_apply, θ_apply_eq_pow πbar jbar hjinj n hpow] at hy
    exact hred.eq_zero y ⟨_, hy⟩
  refine ⟨hinj, ?_⟩
  have : Function.Injective ((πbar.comp jbar : H →ₐ[ZMod p] H).toLinearMap) := hinj
  have hs := (LinearMap.injective_iff_surjective).1 this
  exact hs

end PrimeField

section Assembly

variable (p : ℕ) [Fact p.Prime] (B : Type v) [CommRing B] [HopfAlgebra (ZMod p) B]
  [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]

theorem main :
    ∃ (Bc : Type v) (_ : CommRing Bc) (_ : HopfAlgebra (ZMod p) Bc)
      (_ : Coalgebra.IsCocomm (ZMod p) Bc) (_ : Module.Finite (ZMod p) Bc)
      (Be : Type v) (_ : CommRing Be) (_ : HopfAlgebra (ZMod p) Be)
      (_ : Coalgebra.IsCocomm (ZMod p) Be) (_ : Module.Finite (ZMod p) Be)
      (qc : B →ₐc[ZMod p] Bc) (πe : B →ₐc[ZMod p] Be) (σ : Be →ₐc[ZMod p] B)
      (Θ : B →ₐc[ZMod p] Bc ⊗[ZMod p] Be),
      IsLocalRing Bc ∧ IsReduced Be ∧ Algebra.FormallyUnramified (ZMod p) Be ∧
      Function.Surjective qc ∧ Function.Surjective πe ∧
      RingHom.ker (πe : B →ₐ[ZMod p] Be) = nilradical B ∧
      πe.comp σ = BialgHom.id (ZMod p) Be ∧
      (∀ τ : Be →ₐ[ZMod p] B, (πe : B →ₐ[ZMod p] Be).comp τ = AlgHom.id (ZMod p) Be →
        τ = (σ : Be →ₐ[ZMod p] B)) ∧
      RingHom.ker (qc : B →ₐ[ZMod p] Bc) =
        Ideal.map (σ : Be →ₐ[ZMod p] B) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) Be)) ∧
      Function.Bijective Θ ∧
      ∀ b : B, Θ b = Algebra.TensorProduct.map (qc : B →ₐ[ZMod p] Bc) (πe : B →ₐ[ZMod p] Be)
        (Coalgebra.comul (R := ZMod p) b) := by
  classical
  obtain ⟨n, Hbar, _, _, _, _, hred, πbar, jbar, hπsurj, hjinj, hkerπ, hpow⟩ :=
    HopfAlgebra.exists_isReduced_bialgHom_injective_comp_eq_pow_zmodp p B

  have hθbij := θ_bijective hred πbar jbar hjinj n hpow
  let θe : Hbar ≃ₐc[ZMod p] Hbar := BialgEquiv.ofBijective (πbar.comp jbar) hθbij
  have hθe : ∀ y, θe y = πbar (jbar y) := fun y => rfl
  let σ : Hbar →ₐc[ZMod p] B := jbar.comp (θe.symm : Hbar →ₐc[ZMod p] Hbar)
  have hσθ : ∀ z, σ (θe z) = jbar z := by
    intro z
    change jbar (θe.symm (θe z)) = jbar z
    rw [BialgEquiv.symm_apply_apply]
  have hsec : πbar.comp σ = BialgHom.id (ZMod p) Hbar := by
    refine BialgHom.ext fun y => ?_
    change πbar (jbar (θe.symm y)) = y
    rw [← hθe, BialgEquiv.apply_symm_apply]

  haveI : (Jideal σ).IsHopfIdeal' (ZMod p) := isHopfIdeal_J σ

  have hBnt : Nontrivial B := by
    refine ⟨⟨0, 1, fun h01 => ?_⟩⟩
    have := congrArg (counit (R := ZMod p) (A := B)) h01
    rw [map_zero, Bialgebra.counit_one] at this
    exact zero_ne_one this
  haveI : CharP B p := charP_of_injective_algebraMap (algebraMap (ZMod p) B).injective p

  have hnilpow : ∀ d : B, πbar d = 0 → d ^ p ^ n = 0 := by
    intro d hd
    rw [← hpow, hd, map_zero]

  have hpowJ : ∀ b : B, counit (R := ZMod p) b = 0 → b ^ p ^ n ∈ Jideal σ := by
    intro b hb
    rw [← hpow, ← hσθ]
    refine σ_mem_J σ ?_
    rw [hθe, CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply,
      CoalgHomClass.counit_comp_apply, hb]

  have hqcnt : Nontrivial (B ⧸ Jideal σ) := by
    refine ⟨⟨0, 1, fun h01 => ?_⟩⟩
    have := congrArg (counit (R := ZMod p) (A := B ⧸ Jideal σ)) h01
    rw [map_zero, Bialgebra.counit_one] at this
    exact zero_ne_one this
  have hloc : IsLocalRing (B ⧸ Jideal σ) := by
    haveI := hqcnt
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    set c : ZMod p := counit (R := ZMod p) b with hc
    have hb0 : counit (R := ZMod p) (b - algebraMap (ZMod p) B c) = 0 := by
      rw [map_sub, counit_algebraMap, hc, sub_self]
    have hnil : IsNilpotent (Ideal.Quotient.mk (Jideal σ) (b - algebraMap (ZMod p) B c)) :=
      ⟨p ^ n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hpowJ _ hb0⟩
    by_cases hc0 : c = 0
    · right
      have : (1 : B ⧸ Jideal σ) - Ideal.Quotient.mk (Jideal σ) b =
          1 - Ideal.Quotient.mk (Jideal σ) (b - algebraMap (ZMod p) B c) := by
        rw [hc0, map_zero, sub_zero]
      rw [this]
      exact hnil.isUnit_one_sub
    · left
      have hu : IsUnit (Ideal.Quotient.mk (Jideal σ) (algebraMap (ZMod p) B c)) :=
        ((Ne.isUnit hc0).map (algebraMap (ZMod p) B)).map _
      have : Ideal.Quotient.mk (Jideal σ) b =
          Ideal.Quotient.mk (Jideal σ) (algebraMap (ZMod p) B c) +
            Ideal.Quotient.mk (Jideal σ) (b - algebraMap (ZMod p) B c) := by
        rw [← map_add, add_sub_cancel]
      rw [this]
      exact hnil.isUnit_add_left_of_commute hu (Commute.all _ _)

  have huniq : ∀ τ : Hbar →ₐ[ZMod p] B,
      (πbar : B →ₐ[ZMod p] Hbar).comp τ = AlgHom.id (ZMod p) Hbar →
      τ = (σ : Hbar →ₐ[ZMod p] B) := by
    intro τ hτ
    have hτ' : ∀ z, πbar (τ z) = z := fun z => by
      have := AlgHom.congr_fun hτ z
      simpa using this
    refine AlgHom.ext fun y => ?_

    obtain ⟨z, rfl⟩ := hθbij.2 y
    have hzy : (πbar.comp jbar) z = z ^ p ^ n := by
      rw [BialgHom.comp_apply, θ_apply_eq_pow πbar jbar hjinj n hpow]
    rw [hzy, map_pow, BialgHom.coe_toAlgHom, map_pow]
    have hd : (τ z - σ z) ^ p ^ n = 0 := by
      refine hnilpow _ ?_
      rw [map_sub, hτ', sub_eq_zero]
      have := DFunLike.congr_fun hsec z
      simpa using this.symm
    have : τ z = σ z + (τ z - σ z) := by ring
    rw [this, add_pow_char_pow, hd, add_zero]
  refine ⟨B ⧸ Jideal σ, inferInstance, inferInstance, inferInstance, inferInstance,
    Hbar, inferInstance, inferInstance, inferInstance, inferInstance,
    qc σ, πbar, σ, ThetaMap πbar σ, hloc, hred, formallyUnramified_of_isReduced hred,
    qc_surjective σ, hπsurj, hkerπ, hsec, huniq,
    ker_qc σ, ThetaMap_bijective πbar σ hsec, fun b => rfl⟩

end Assembly

end ConnectedEtaleSplitting
p2m_reactivate "P2MW.S_HopfAlgebra_exists_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp.ConnectedEtaleSplitting"

end
p2m_reactivate "P2MW.S_HopfAlgebra_exists_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp.ConnectedEtaleSplitting"

theorem solution
    (p : ℕ) [Fact p.Prime] (B : Type v) [CommRing B] [HopfAlgebra (ZMod p) B]
    [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B] :
    ∃ (Bc : Type v) (_ : CommRing Bc) (_ : HopfAlgebra (ZMod p) Bc)
      (_ : Coalgebra.IsCocomm (ZMod p) Bc) (_ : Module.Finite (ZMod p) Bc)
      (Be : Type v) (_ : CommRing Be) (_ : HopfAlgebra (ZMod p) Be)
      (_ : Coalgebra.IsCocomm (ZMod p) Be) (_ : Module.Finite (ZMod p) Be)
      (qc : B →ₐc[ZMod p] Bc) (πe : B →ₐc[ZMod p] Be) (σ : Be →ₐc[ZMod p] B)
      (Θ : B →ₐc[ZMod p] Bc ⊗[ZMod p] Be),
      IsLocalRing Bc ∧ IsReduced Be ∧ Algebra.FormallyUnramified (ZMod p) Be ∧
      Function.Surjective qc ∧ Function.Surjective πe ∧
      RingHom.ker (πe : B →ₐ[ZMod p] Be) = nilradical B ∧
      πe.comp σ = BialgHom.id (ZMod p) Be ∧
      (∀ τ : Be →ₐ[ZMod p] B, (πe : B →ₐ[ZMod p] Be).comp τ = AlgHom.id (ZMod p) Be →
        τ = (σ : Be →ₐ[ZMod p] B)) ∧
      RingHom.ker (qc : B →ₐ[ZMod p] Bc) =
        Ideal.map (σ : Be →ₐ[ZMod p] B) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) Be)) ∧
      Function.Bijective Θ ∧
      ∀ b : B, Θ b = Algebra.TensorProduct.map (qc : B →ₐ[ZMod p] Bc) (πe : B →ₐ[ZMod p] Be)
        (Coalgebra.comul (R := ZMod p) b) :=
  ConnectedEtaleSplitting.main p B

end S_HopfAlgebra_exists_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp
end P2MW
export P2MW.S_HopfAlgebra_exists_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp (solution)
