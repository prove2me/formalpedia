-- Prove2me | solution 1 for HopfAlgebra.faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7c6c8590-653d-542a-a014-a52f61be1baf

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_hopfKer_baseChange_toSubmodule_eq_range_baseChange
import Theorems.Thm_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent

set_option autoImplicit false
open scoped TensorProduct

universe u v w

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk coaction hopfKer mem_hopfKer_iff coaction_eq_of_mem hopfKer_baseChange_toSubmodule_eq_range_baseChange faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite"
namespace S5
p2m_open "HopfAlgebra"

section E1

variable {R : Type u} [CommRing R] (K : Type u) [CommRing K] [Algebra R K] [Module.Flat R K]
  {H : Type v} [CommRing H] [HopfAlgebra R H] {H' : Type w} [CommRing H'] [HopfAlgebra R H']
  (qc : H →ₐc[R] H')

noncomputable abbrev qcK : K ⊗[R] H →ₐc[K] K ⊗[R] H' :=
  (Bialgebra.TensorProduct.map (BialgHom.id K K) qc : K ⊗[R] H →ₐc[K] K ⊗[R] H')

noncomputable def kerBaseChange : K ⊗[R] ↥(HopfAlgebra.hopfKer qc) →ₐ[K] K ⊗[R] H :=
  Algebra.TensorProduct.map (AlgHom.id K K) (HopfAlgebra.hopfKer qc).val

theorem kerBaseChange_tmul (k : K) (b : ↥(HopfAlgebra.hopfKer qc)) :
    kerBaseChange K qc (k ⊗ₜ[R] b) = k ⊗ₜ[R] (b : H) := rfl

theorem kerBaseChange_toLinearMap :
    (kerBaseChange K qc).toLinearMap = (HopfAlgebra.hopfKer qc).val.toLinearMap.baseChange K := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro k b
  rfl

theorem kerBaseChange_injective : Function.Injective (kerBaseChange K qc) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := K)
    (HopfAlgebra.hopfKer qc).val.toLinearMap Subtype.val_injective
  intro x y hxy
  apply h
  have e1 : ∀ z, (HopfAlgebra.hopfKer qc).val.toLinearMap.lTensor K z = kerBaseChange K qc z := fun z => by
    rw [← LinearMap.baseChange_eq_ltensor, ← kerBaseChange_toLinearMap]; rfl
  rw [e1, e1]; exact hxy

theorem kerBaseChange_mem (x : K ⊗[R] ↥(HopfAlgebra.hopfKer qc)) :
    kerBaseChange K qc x ∈ HopfAlgebra.hopfKer (qcK K qc) := by
  have h := HopfAlgebra.hopfKer_baseChange_toSubmodule_eq_range_baseChange K qc
  have : kerBaseChange K qc x ∈ LinearMap.range ((HopfAlgebra.hopfKer qc).val.toLinearMap.baseChange K) :=
    ⟨x, by rw [← kerBaseChange_toLinearMap]; rfl⟩
  rw [← h] at this
  exact this

theorem kerBaseChange_surj (y : K ⊗[R] H) (hy : y ∈ HopfAlgebra.hopfKer (qcK K qc)) :
    ∃ x, kerBaseChange K qc x = y := by
  have h := HopfAlgebra.hopfKer_baseChange_toSubmodule_eq_range_baseChange K qc
  have hy' : y ∈ Subalgebra.toSubmodule (HopfAlgebra.hopfKer (qcK K qc)) := hy
  rw [h] at hy'
  obtain ⟨x, hx⟩ := hy'
  exact ⟨x, by rw [← hx, ← kerBaseChange_toLinearMap]; rfl⟩

noncomputable def eB : K ⊗[R] ↥(HopfAlgebra.hopfKer qc) ≃ₐ[K] ↥(HopfAlgebra.hopfKer (qcK K qc)) :=
  AlgEquiv.ofBijective ((kerBaseChange K qc).codRestrict (HopfAlgebra.hopfKer (qcK K qc)) (kerBaseChange_mem K qc))
    ⟨fun x y hxy => kerBaseChange_injective K qc (congrArg Subtype.val hxy),
     fun y => by obtain ⟨x, hx⟩ := kerBaseChange_surj K qc y.1 y.2; exact ⟨x, Subtype.ext hx⟩⟩

@[scoped simp] theorem coe_eB (x : K ⊗[R] ↥(HopfAlgebra.hopfKer qc)) :
    ((eB K qc x : ↥(HopfAlgebra.hopfKer (qcK K qc))) : K ⊗[R] H) = kerBaseChange K qc x := rfl

theorem coe_eB_tmul (k : K) (b : ↥(HopfAlgebra.hopfKer qc)) :
    ((eB K qc (k ⊗ₜ[R] b) : ↥(HopfAlgebra.hopfKer (qcK K qc))) : K ⊗[R] H) = k ⊗ₜ[R] (b : H) := rfl

end E1

end HopfAlgebra.S5
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra.S5"
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk coaction hopfKer mem_hopfKer_iff coaction_eq_of_mem hopfKer_baseChange_toSubmodule_eq_range_baseChange faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite"
namespace S5
p2m_open "HopfAlgebra"

section E2

variable {R : Type u} [CommRing R] (K : Type u) [CommRing K] [Algebra R K]
  {H : Type v} [CommRing H] [HopfAlgebra R H] {H' : Type w} [CommRing H'] [HopfAlgebra R H']
  (qc : H →ₐc[R] H')

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 1600000 in

noncomputable def iotaE2
    (eB : K ⊗[R] ↥(HopfAlgebra.hopfKer qc) ≃ₐ[K] ↥(HopfAlgebra.hopfKer (qcK K qc)))
    (heB : ∀ (k : K) (b : ↥(HopfAlgebra.hopfKer qc)),
      ((eB (k ⊗ₜ[R] b) : ↥(HopfAlgebra.hopfKer (qcK K qc))) : K ⊗[R] H) = k ⊗ₜ[R] (b : H)) :
    letI algBBK := ((((eB : K ⊗[R] ↥(HopfAlgebra.hopfKer qc) →ₐ[K] ↥(HopfAlgebra.hopfKer (qcK K qc))).restrictScalars R).comp
        Algebra.TensorProduct.includeRight).toRingHom.toAlgebra :
          Algebra ↥(HopfAlgebra.hopfKer qc) ↥(HopfAlgebra.hopfKer (qcK K qc)));
    letI algBHK := (((Algebra.TensorProduct.includeRight : H →ₐ[R] K ⊗[R] H).comp
        (HopfAlgebra.hopfKer qc).val).toRingHom.toAlgebra : Algebra ↥(HopfAlgebra.hopfKer qc) (K ⊗[R] H));
    (↥(HopfAlgebra.hopfKer (qcK K qc)) ⊗[↥(HopfAlgebra.hopfKer qc)] H ≃ₗ[↥(HopfAlgebra.hopfKer (qcK K qc))]
      (K ⊗[R] H)) := by
  letI algBBK : Algebra ↥(HopfAlgebra.hopfKer qc) ↥(HopfAlgebra.hopfKer (qcK K qc)) :=
    (((eB : K ⊗[R] ↥(HopfAlgebra.hopfKer qc) →ₐ[K] ↥(HopfAlgebra.hopfKer (qcK K qc))).restrictScalars R).comp Algebra.TensorProduct.includeRight).toRingHom.toAlgebra
  letI algBHK : Algebra ↥(HopfAlgebra.hopfKer qc) (K ⊗[R] H) :=
    ((Algebra.TensorProduct.includeRight : H →ₐ[R] K ⊗[R] H).comp (HopfAlgebra.hopfKer qc).val).toRingHom.toAlgebra
  have halgBBK : ∀ b : ↥(HopfAlgebra.hopfKer qc), algebraMap ↥(HopfAlgebra.hopfKer qc) ↥(HopfAlgebra.hopfKer (qcK K qc)) b = eB ((1 : K) ⊗ₜ[R] b) := fun _ => rfl
  have halgBHK : ∀ b : ↥(HopfAlgebra.hopfKer qc), algebraMap ↥(HopfAlgebra.hopfKer qc) (K ⊗[R] H) b = (1 : K) ⊗ₜ[R] (b : H) := fun _ => rfl
  have halgBKHK : ∀ x : ↥(HopfAlgebra.hopfKer (qcK K qc)), algebraMap ↥(HopfAlgebra.hopfKer (qcK K qc)) (K ⊗[R] H) x = (x : K ⊗[R] H) := fun _ => rfl
  haveI : IsScalarTower ↥(HopfAlgebra.hopfKer qc) ↥(HopfAlgebra.hopfKer (qcK K qc)) (K ⊗[R] H) := IsScalarTower.of_algebraMap_eq fun b => by
    rw [halgBHK, halgBKHK, halgBBK, heB]

  let g : H →ₐ[↥(HopfAlgebra.hopfKer qc)] K ⊗[R] H :=
    { (Algebra.TensorProduct.includeRight : H →ₐ[R] K ⊗[R] H).toRingHom with
      commutes' := fun b => rfl }
  have hg : ∀ h : H, g h = (1 : K) ⊗ₜ[R] h := fun _ => rfl

  let ψ : ↥(HopfAlgebra.hopfKer (qcK K qc)) ⊗[↥(HopfAlgebra.hopfKer qc)] H →ₐ[↥(HopfAlgebra.hopfKer (qcK K qc))] K ⊗[R] H :=
    Algebra.TensorProduct.lift (Algebra.ofId ↥(HopfAlgebra.hopfKer (qcK K qc)) (K ⊗[R] H)) g (fun _ _ => Commute.all _ _)
  have hψ : ∀ (x : ↥(HopfAlgebra.hopfKer (qcK K qc))) (h : H), ψ (x ⊗ₜ[↥(HopfAlgebra.hopfKer qc)] h) = (x : K ⊗[R] H) * ((1 : K) ⊗ₜ[R] h) := fun x h => by
    show Algebra.TensorProduct.lift _ g _ (x ⊗ₜ h) = _
    rw [Algebra.TensorProduct.lift_tmul]
    rfl

  have hKmem : ∀ k : K, k ⊗ₜ[R] (1 : H) ∈ HopfAlgebra.hopfKer (qcK K qc) := fun k => by
    have := (HopfAlgebra.hopfKer (qcK K qc)).algebraMap_mem k
    rwa [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at this
  let ιK : K → ↥(HopfAlgebra.hopfKer (qcK K qc)) := fun k => ⟨k ⊗ₜ[R] 1, hKmem k⟩

  have hsurj : Function.Surjective ψ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul k h =>
        refine ⟨ιK k ⊗ₜ[↥(HopfAlgebra.hopfKer qc)] h, ?_⟩
        rw [hψ]
        show (k ⊗ₜ[R] (1 : H)) * ((1 : K) ⊗ₜ[R] h) = k ⊗ₜ[R] h
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact ⟨a + b, map_add _ _ _⟩

  have hbal : ∀ (r : R) (k : K) (h : H), ιK (r • k) ⊗ₜ[↥(HopfAlgebra.hopfKer qc)] h = ιK k ⊗ₜ[↥(HopfAlgebra.hopfKer qc)] (r • h) := by
    intro r k h
    have h1 : r • h = (algebraMap R ↥(HopfAlgebra.hopfKer qc) r) • h := by
      rw [Algebra.smul_def, Algebra.smul_def]
      rfl
    have h2 : ιK (r • k) = (algebraMap R ↥(HopfAlgebra.hopfKer qc) r) • ιK k := by
      rw [Algebra.smul_def (algebraMap R ↥(HopfAlgebra.hopfKer qc) r), halgBBK]
      apply Subtype.ext
      show (r • k) ⊗ₜ[R] (1 : H) = ((eB ((1 : K) ⊗ₜ[R] algebraMap R ↥(HopfAlgebra.hopfKer qc) r) : ↥(HopfAlgebra.hopfKer (qcK K qc))) : K ⊗[R] H) * (k ⊗ₜ[R] 1)
      rw [heB, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      show (r • k) ⊗ₜ[R] (1 : H) = k ⊗ₜ[R] (algebraMap R H r)
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [h1, h2, TensorProduct.smul_tmul]
  let θ : K ⊗[R] H →+ ↥(HopfAlgebra.hopfKer (qcK K qc)) ⊗[↥(HopfAlgebra.hopfKer qc)] H :=
    TensorProduct.liftAddHom
      { toFun := fun k => { toFun := fun h => ιK k ⊗ₜ[↥(HopfAlgebra.hopfKer qc)] h
                            map_zero' := by simp
                            map_add' := fun _ _ => TensorProduct.tmul_add _ _ _ }
        map_zero' := by
          ext h
          show ιK 0 ⊗ₜ[↥(HopfAlgebra.hopfKer qc)] h = 0
          have : ιK 0 = 0 := Subtype.ext (by show (0 : K) ⊗ₜ[R] (1 : H) = 0; simp)
          rw [this, TensorProduct.zero_tmul]
        map_add' := fun k k' => by
          ext h
          show ιK (k + k') ⊗ₜ[↥(HopfAlgebra.hopfKer qc)] h = ιK k ⊗ₜ[↥(HopfAlgebra.hopfKer qc)] h + ιK k' ⊗ₜ[↥(HopfAlgebra.hopfKer qc)] h
          have : ιK (k + k') = ιK k + ιK k' := Subtype.ext (TensorProduct.add_tmul _ _ _)
          rw [this, TensorProduct.add_tmul] }
      (fun r k h => hbal r k h)
  have hθ : ∀ (k : K) (h : H), θ (k ⊗ₜ[R] h) = ιK k ⊗ₜ[↥(HopfAlgebra.hopfKer qc)] h := fun k h => by
    show TensorProduct.liftAddHom _ _ (k ⊗ₜ h) = _
    rw [TensorProduct.liftAddHom_tmul]
    rfl

  have hleft : ∀ z : ↥(HopfAlgebra.hopfKer (qcK K qc)) ⊗[↥(HopfAlgebra.hopfKer qc)] H, θ (ψ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x h =>
        obtain ⟨t, rfl⟩ := eB.surjective x
        induction t using TensorProduct.induction_on with
        | zero => rw [map_zero, TensorProduct.zero_tmul, map_zero, map_zero]
        | tmul k b =>
            rw [hψ, heB, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hθ]

            have h3 : (b : H) * h = b • h := rfl
            rw [h3, ← TensorProduct.smul_tmul]
            congr 1
            rw [Algebra.smul_def, halgBBK]
            apply Subtype.ext
            show ((eB ((1 : K) ⊗ₜ[R] b) : ↥(HopfAlgebra.hopfKer (qcK K qc))) : K ⊗[R] H) * (k ⊗ₜ[R] 1) = ((eB (k ⊗ₜ[R] b) : ↥(HopfAlgebra.hopfKer (qcK K qc))) : K ⊗[R] H)
            rw [heB, heB, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        | add t₁ t₂ h₁ h₂ =>
            rw [map_add, TensorProduct.add_tmul, map_add, map_add, h₁, h₂]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hinj : Function.Injective ψ := fun x y hxy => by
    have := congrArg θ hxy
    rwa [hleft, hleft] at this
  exact LinearEquiv.ofBijective ψ.toLinearMap ⟨hinj, hsurj⟩

end E2
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra.S5"

end HopfAlgebra.S5
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra.S5"
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra.S5"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk coaction hopfKer mem_hopfKer_iff coaction_eq_of_mem hopfKer_baseChange_toSubmodule_eq_range_baseChange faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite"
namespace S5
p2m_open "HopfAlgebra"

theorem pow_eq_of_isIdempotentElem {M : Type*} [MonoidWithZero M] {a : M} (ha : IsIdempotentElem a) (n : ℕ) (hn : 1 ≤ n) :
    a ^ n = a := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact ha.pow_succ_eq m

theorem exists_algebraMap_mul_eq_one_sub
    {R H : Type*} [CommRing R] [IsLocalRing R] [CommRing H] [Algebra R H]
    (e f : H) (he : IsIdempotentElem e) (hf : IsIdempotentElem f) (hfe : f * e = e)
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤)
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}) :
    ∃ u : H, algebraMap R H π * u = 1 - f := by
  set s : H := 1 - e with hs
  have hsid : IsIdempotentElem s := he.one_sub
  set x : H := algebraMap R H π with hx

  have hunit : IsUnit (algebraMap H (Localization.Away s) x) := by
    rw [hπ, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top] at hgen
    rwa [hx, ← IsScalarTower.algebraMap_apply]
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  obtain ⟨⟨h, ⟨_, n, rfl⟩⟩, hhv⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) v

  have h1 : algebraMap H (Localization.Away s) (x * h) = algebraMap H (Localization.Away s) (s ^ n) := by
    rw [← hhv, IsLocalization.mul_mk'_eq_mk'_of_mul] at hv
    rw [IsLocalization.mk'_eq_iff_eq_mul, one_mul] at hv
    exact hv
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers s) (Localization.Away s)).mp h1

  have h2 : s * (x * h) = s := by
    have hm' : s ^ m * (x * h) = s ^ m * s ^ n := hm
    calc s * (x * h) = s ^ (m + 1) * (x * h) := by rw [pow_eq_of_isIdempotentElem hsid (m + 1) (by omega)]
      _ = s * (s ^ m * (x * h)) := by ring
      _ = s * (s ^ m * s ^ n) := by rw [hm']
      _ = s ^ (m + n + 1) := by ring
      _ = s := pow_eq_of_isIdempotentElem hsid _ (by omega)
  refine ⟨h * s * (1 - f), ?_⟩
  have h3 : (1 - f) * s = 1 - f := by
    rw [hs]; ring_nf
    have : f * e = e := hfe
    linear_combination this
  calc x * (h * s * (1 - f)) = (s * (x * h)) * (1 - f) := by ring
    _ = s * (1 - f) := by rw [h2]
    _ = 1 - f := by rw [mul_comm, h3]

theorem mem_hopfKer_of_algebraMap_mul_eq_one_sub
    {R : Type*} [CommRing R] [IsDomain R] {H H' : Type*} [CommRing H] [CommRing H']
    [HopfAlgebra R H] [HopfAlgebra R H'] [Module.Flat R H] [Module.Flat R H']
    (qc : H →ₐc[R] H') (f : H) (hfK : f ∈ HopfAlgebra.hopfKer qc) (r : R) (hr : r ≠ 0)
    (u : H) (hu : algebraMap R H r * u = 1 - f) : u ∈ HopfAlgebra.hopfKer qc := by
  rw [HopfAlgebra.mem_hopfKer_iff]
  have h1f : (1 - f) ∈ HopfAlgebra.hopfKer qc := Subalgebra.sub_mem _ (Subalgebra.one_mem _) hfK
  have hsmul : r • u = 1 - f := by rw [Algebra.smul_def, hu]

  have hw : r • (HopfAlgebra.coaction qc u - u ⊗ₜ[R] 1) = 0 := by
    rw [smul_sub, ← map_smul, hsmul, HopfAlgebra.coaction_eq_of_mem qc h1f, TensorProduct.smul_tmul', hsmul, sub_self]

  have hreg : IsSMulRegular (H ⊗[R] H') r :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr)
  have : HopfAlgebra.coaction qc u - u ⊗ₜ[R] 1 = 0 := hreg (by
    show r • (HopfAlgebra.coaction qc u - u ⊗ₜ[R] 1) = r • (0 : H ⊗[R] H')
    rw [hw, smul_zero])
  exact sub_eq_zero.mp this

theorem isUnit_algebraMap_hopfKer_quotient_span
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Flat R H]
    (H' : Type) [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H')
    (e : H) (he : IsIdempotentElem e)
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤)
    (f : H) (hf : IsIdempotentElem f) (hfK : f ∈ HopfAlgebra.hopfKer qc) (hfe : f * e = e)
    (r : R) (hr : r ≠ 0) :
    IsUnit (algebraMap R (↥(HopfAlgebra.hopfKer qc) ⧸ Ideal.span {(⟨f, hfK⟩ : ↥(HopfAlgebra.hopfKer qc))}) r) := by
  set B := ↥(HopfAlgebra.hopfKer qc) with hB
  set fB : B := ⟨f, hfK⟩ with hfB
  by_cases h𝔪 : IsLocalRing.maximalIdeal R = ⊥
  ·
    have hfield : IsField R := (IsLocalRing.isField_iff_maximalIdeal_eq).mpr h𝔪
    have hru : IsUnit r := by
      letI := hfield.toField
      exact isUnit_iff_ne_zero.mpr hr
    exact hru.map _
  ·
    haveI : IsDiscreteValuationRing R := { not_a_field' := h𝔪 }
    obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hπmax : IsLocalRing.maximalIdeal R = Ideal.span {π} := hπirr.maximalIdeal_eq
    have hπ0 : π ≠ 0 := hπirr.ne_zero
    obtain ⟨n, v, hrv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hπirr

    obtain ⟨u, hu⟩ := exists_algebraMap_mul_eq_one_sub e f he hf hfe hgen π hπmax
    have huK : u ∈ HopfAlgebra.hopfKer qc := mem_hopfKer_of_algebraMap_mul_eq_one_sub qc f hfK π hπ0 u hu
    have hπB : algebraMap R B π * ⟨u, huK⟩ = 1 - fB := by
      apply Subtype.ext
      exact hu
    have hπunit : IsUnit (algebraMap R (B ⧸ Ideal.span {fB}) π) := by
      rw [IsScalarTower.algebraMap_apply R B (B ⧸ Ideal.span {fB})]
      refine isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk (Ideal.span {fB}) ⟨u, huK⟩, ?_⟩
      rw [Ideal.Quotient.algebraMap_eq, ← map_mul, hπB, map_sub, map_one,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self fB), sub_zero]
    rw [hrv, map_mul, map_pow]
    exact ((v.isUnit).map _).mul (hπunit.pow n)

end HopfAlgebra.S5
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra.S5"
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra.S5"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk coaction hopfKer mem_hopfKer_iff coaction_eq_of_mem hopfKer_baseChange_toSubmodule_eq_range_baseChange faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite"
namespace S5
p2m_open "HopfAlgebra"

theorem faithfullyFlat_baseChange_of_linearEquiv
    {B BK Q : Type*} [CommRing B] [CommRing BK] [CommRing Q] [Algebra B BK] [Algebra BK Q] [Algebra B Q]
    [IsScalarTower B BK Q]
    {H : Type*} [AddCommGroup H] [Module B H]
    {HK : Type*} [AddCommGroup HK] [Module BK HK] [Module B HK] [IsScalarTower B BK HK]
    (ι : BK ⊗[B] H ≃ₗ[BK] HK) [Module.FaithfullyFlat BK HK] :
    Module.FaithfullyFlat Q (Q ⊗[B] H) := by

  haveI : Module.FaithfullyFlat Q (Q ⊗[BK] HK) := inferInstance

  let e₁ : Q ⊗[BK] HK ≃ₗ[Q] Q ⊗[BK] (BK ⊗[B] H) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Q Q) ι.symm
  let e₂ : Q ⊗[BK] (BK ⊗[B] H) ≃ₗ[Q] Q ⊗[B] H :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange B BK Q Q H
  exact Module.FaithfullyFlat.of_linearEquiv Q (Q ⊗[BK] HK) (e₁.trans e₂).symm

end HopfAlgebra.S5
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra.S5"
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra.S5"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk coaction hopfKer mem_hopfKer_iff coaction_eq_of_mem hopfKer_baseChange_toSubmodule_eq_range_baseChange faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite"
namespace S5
p2m_open "HopfAlgebra"
open scoped TensorProduct

set_option maxHeartbeats 1600000 in
theorem faithfullyFlat_hopfKer_baseChange_field
    (R : Type) [CommRing R] [IsDomain R]
    (K : Type) [Field K] [Algebra R K]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite K (K ⊗[R] H)]
    (H' : Type) [CommRing H'] [HopfAlgebra R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc) :
    Module.FaithfullyFlat
      ↥(HopfAlgebra.hopfKer (Bialgebra.TensorProduct.map (BialgHom.id K K) qc :
          K ⊗[R] H →ₐc[K] K ⊗[R] H'))
      (K ⊗[R] H) := by
  set qcK : K ⊗[R] H →ₐc[K] K ⊗[R] H' := Bialgebra.TensorProduct.map (BialgHom.id K K) qc with hqcK
  have hsurjK : Function.Surjective qcK := by
    have h1 : ∀ x, qcK x = (qc : H →ₐc[R] H').toLinearMap.lTensor K x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul k h => simp [qcK]; rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    intro y
    obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective K hqc y
    exact ⟨x, (h1 x).trans hx⟩
  haveI : Module.Finite K (K ⊗[R] H') := Module.Finite.of_surjective (qcK : K ⊗[R] H →ₐc[K] K ⊗[R] H').toLinearMap hsurjK
  haveI : Module.Flat K (K ⊗[R] H') := inferInstance
  exact HopfAlgebra.faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite K (K ⊗[R] H)
    (K ⊗[R] H') qcK hsurjK

end HopfAlgebra.S5
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra.S5"
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra.S5"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk coaction hopfKer mem_hopfKer_iff coaction_eq_of_mem hopfKer_baseChange_toSubmodule_eq_range_baseChange faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite"
namespace S5
p2m_open "HopfAlgebra"
open scoped TensorProduct

theorem exists_ringHom_comp_algebraMap_eq
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Flat R H]
    (H' : Type) [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H')
    (e : H) (he : IsIdempotentElem e)
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤)
    (f : H) (hf : IsIdempotentElem f) (hfK : f ∈ HopfAlgebra.hopfKer qc) (hfe : f * e = e) :
    ∃ θ : K →+* (↥(HopfAlgebra.hopfKer qc) ⧸ Ideal.span {(⟨f, hfK⟩ : ↥(HopfAlgebra.hopfKer qc))}),
      θ.comp (algebraMap R K) = algebraMap R _ := by
  have hunit : ∀ y : nonZeroDivisors R,
      IsUnit (algebraMap R (↥(HopfAlgebra.hopfKer qc) ⧸ Ideal.span {(⟨f, hfK⟩ : ↥(HopfAlgebra.hopfKer qc))}) y) :=
    fun y => isUnit_algebraMap_hopfKer_quotient_span R H H' qc e he hgen f hf hfK hfe y.1
      (nonZeroDivisors.ne_zero y.2)
  refine ⟨IsLocalization.lift (M := nonZeroDivisors R) (S := K) hunit, ?_⟩
  ext r
  simp [IsLocalization.lift_eq]

end HopfAlgebra.S5
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra.S5"
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra.S5"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk coaction hopfKer mem_hopfKer_iff coaction_eq_of_mem hopfKer_baseChange_toSubmodule_eq_range_baseChange faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite"
namespace S5
p2m_open "HopfAlgebra"
open scoped TensorProduct

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 320000 in
theorem main_of

    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H] [Module.Finite K (TensorProduct R K H)]
    (H' : Type) [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc)
    (e : H) (he : IsIdempotentElem e) (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤)
    (e' : H') (he' : IsIdempotentElem e') (hfin' : Module.Finite R (Localization.Away e'))
    (hgen' : Ideal.map (algebraMap R (Localization.Away (1 - e'))) (IsLocalRing.maximalIdeal R) = ⊤)
    (hee' : qc e = e')
    (f : H) (hf : IsIdempotentElem f) (hfK : f ∈ HopfAlgebra.hopfKer qc) (hfe : f * e = e)
    (hmin : ∀ b ∈ HopfAlgebra.hopfKer qc, b * e = 0 → b * f = 0)
    (eB : K ⊗[R] ↥(HopfAlgebra.hopfKer qc) ≃ₐ[K]
      ↥(HopfAlgebra.hopfKer (Bialgebra.TensorProduct.map (BialgHom.id K K) qc :
          K ⊗[R] H →ₐc[K] K ⊗[R] H')))
    (heB : ∀ (k : K) (b : ↥(HopfAlgebra.hopfKer qc)),
      ((eB (k ⊗ₜ[R] b) : ↥(HopfAlgebra.hopfKer (Bialgebra.TensorProduct.map (BialgHom.id K K) qc :
          K ⊗[R] H →ₐc[K] K ⊗[R] H'))) : K ⊗[R] H) = k ⊗ₜ[R] (b : H)) :
    Module.FaithfullyFlat (↥(HopfAlgebra.hopfKer qc) ⧸ Ideal.span {(⟨f, hfK⟩ : ↥(HopfAlgebra.hopfKer qc))})
      (TensorProduct ↥(HopfAlgebra.hopfKer qc)
        (↥(HopfAlgebra.hopfKer qc) ⧸ Ideal.span {(⟨f, hfK⟩ : ↥(HopfAlgebra.hopfKer qc))}) H) := by
  classical

  let qcK : K ⊗[R] H →ₐc[K] K ⊗[R] H' := Bialgebra.TensorProduct.map (BialgHom.id K K) qc
  let B : Type := ↥(HopfAlgebra.hopfKer qc)
  let BK : Type := ↥(HopfAlgebra.hopfKer qcK)
  let fB : B := ⟨f, hfK⟩
  let Q : Type := B ⧸ Ideal.span {fB}

  haveI hFFK : Module.FaithfullyFlat BK (K ⊗[R] H) := faithfullyFlat_hopfKer_baseChange_field R K H H' qc hqc

  obtain ⟨θK, hθK⟩ := exists_ringHom_comp_algebraMap_eq R K H H' qc e he hgen f hf hfK hfe
  letI : Algebra K Q := θK.toAlgebra
  haveI : IsScalarTower R K Q :=
    IsScalarTower.of_algebraMap_eq fun r => (RingHom.congr_fun hθK r).symm

  let θ0 : K ⊗[R] B →ₐ[R] Q :=
    Algebra.TensorProduct.lift ((Algebra.ofId K Q).restrictScalars R) (Ideal.Quotient.mkₐ R (Ideal.span {fB}))
      (fun _ _ => Commute.all _ _)
  let θ : BK →+* Q := θ0.toRingHom.comp (eB.symm : BK →ₐ[K] K ⊗[R] B).toRingHom
  letI algBKQ : Algebra BK Q := θ.toAlgebra

  let jB : B →ₐ[R] BK := ((eB : K ⊗[R] B →ₐ[K] BK).restrictScalars R).comp Algebra.TensorProduct.includeRight
  letI algBBK : Algebra B BK := jB.toRingHom.toAlgebra
  letI algBHK : Algebra B (K ⊗[R] H) :=
    ((Algebra.TensorProduct.includeRight : H →ₐ[R] K ⊗[R] H).comp (HopfAlgebra.hopfKer qc).val).toRingHom.toAlgebra
  have halgBBK : ∀ b : B, ((algebraMap B BK b : BK) : K ⊗[R] H) = (1 : K) ⊗ₜ[R] (b : H) := by
    intro b
    show ((eB ((1 : K) ⊗ₜ[R] b) : BK) : K ⊗[R] H) = _
    exact heB 1 b
  have halgBHK : ∀ b : B, algebraMap B (K ⊗[R] H) b = (1 : K) ⊗ₜ[R] (b : H) := fun b => rfl
  haveI : IsScalarTower B BK (K ⊗[R] H) := by
    apply IsScalarTower.of_algebraMap_eq
    intro b
    rw [halgBHK]
    exact (halgBBK b).symm
  haveI : IsScalarTower B BK Q := by
    apply IsScalarTower.of_algebraMap_eq
    intro b
    change Ideal.Quotient.mk (Ideal.span {fB}) b = θ0 (eB.symm (eB ((1 : K) ⊗ₜ[R] b)))
    rw [AlgEquiv.symm_apply_apply]
    change _ = Algebra.TensorProduct.lift ((Algebra.ofId K Q).restrictScalars R)
      (Ideal.Quotient.mkₐ R (Ideal.span {fB})) (fun _ _ => Commute.all _ _) ((1 : K) ⊗ₜ[R] b)
    rw [Algebra.TensorProduct.lift_tmul]
    change _ = algebraMap K Q 1 * Ideal.Quotient.mk (Ideal.span {fB}) b
    rw [map_one, one_mul]

  have ι : BK ⊗[B] H ≃ₗ[BK] (K ⊗[R] H) := iotaE2 K qc eB heB
  exact faithfullyFlat_baseChange_of_linearEquiv (B := B) (BK := BK) (Q := Q) (H := H) (HK := K ⊗[R] H) ι

end HopfAlgebra.S5
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra.S5"
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.HopfAlgebra.S5"

theorem solution

    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H] [Module.Finite K (TensorProduct R K H)]
    (H' : Type) [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc)
    (e : H) (he : IsIdempotentElem e) (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤)
    (e' : H') (he' : IsIdempotentElem e') (hfin' : Module.Finite R (Localization.Away e'))
    (hgen' : Ideal.map (algebraMap R (Localization.Away (1 - e'))) (IsLocalRing.maximalIdeal R) = ⊤)
    (hee' : qc e = e')
    (f : H) (hf : IsIdempotentElem f) (hfK : f ∈ HopfAlgebra.hopfKer qc) (hfe : f * e = e)
    (hmin : ∀ b ∈ HopfAlgebra.hopfKer qc, b * e = 0 → b * f = 0) :
    Module.FaithfullyFlat (↥(HopfAlgebra.hopfKer qc) ⧸ Ideal.span {(⟨f, hfK⟩ : ↥(HopfAlgebra.hopfKer qc))})
      (TensorProduct ↥(HopfAlgebra.hopfKer qc)
        (↥(HopfAlgebra.hopfKer qc) ⧸ Ideal.span {(⟨f, hfK⟩ : ↥(HopfAlgebra.hopfKer qc))}) H)  := by
  exact HopfAlgebra.S5.main_of R K H H' qc hqc e he hfin hgen e' he' hfin' hgen' hee' f hf hfK hfe hmin
    (HopfAlgebra.S5.eB K qc) (fun k b => HopfAlgebra.S5.coe_eB_tmul K qc k b)

end S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent
end P2MW
export P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent (solution)
