-- Prove2me | solution 1 for HopfAlgebra.faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/62e34ffd-8890-5efa-9c0c-589f4500cda6

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem
import Theorems.Thm_Module_Flat_of_forall_flat_residueField_tensorProduct_of_isPrincipalIdealRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct
p2m_open "HopfAlgebra P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing.HopfAlgebra"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "hopfKer mem_hopfKer_iff HopfKerHopf.antipode_mem HopfKerHopf.ι₂_tmul HopfKerHopf.comul_coe_mem_range faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem"
namespace FFHopfKerPID
p2m_open "HopfAlgebra"

universe u

section Saturation

variable {R : Type} [CommRing R] [IsDomain R]
variable {H : Type} [CommRing H] [HopfAlgebra R H]
variable {H' : Type} [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H] [Module.Flat R H']
variable (qc : H →ₐc[R] H')

theorem mem_hopfKer_of_smul_mem {t : R} (ht : t ≠ 0) {h : H} (hth : t • h ∈ hopfKer qc) :
    h ∈ hopfKer qc := by
  rw [mem_hopfKer_iff] at hth ⊢
  have hreg : IsSMulRegular (H ⊗[R] H') t :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ht)
  apply hreg
  simp only
  rw [← map_smul, hth, TensorProduct.smul_tmul']

example [IsDedekindDomain R] : Module.Flat R ↥(hopfKer qc) := inferInstance

end Saturation

section Fibre

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {H : Type} [CommRing H] [HopfAlgebra R H] [Module.Flat R H]
variable {H' : Type} [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
variable (qc : H →ₐc[R] H') (p : Ideal R) [p.IsPrime]

noncomputable def φ : p.ResidueField ⊗[R] ↥(hopfKer qc) →ₐ[p.ResidueField] p.ResidueField ⊗[R] H :=
  Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
    (IsScalarTower.toAlgHom R ↥(hopfKer qc) H)

@[scoped simp] theorem φ_tmul (c : p.ResidueField) (k : ↥(hopfKer qc)) :
    φ qc p (c ⊗ₜ[R] k) = c ⊗ₜ[R] (k : H) := rfl

theorem φ_apply_eq_lTensor (z : p.ResidueField ⊗[R] ↥(hopfKer qc)) :
    φ qc p z = ((hopfKer qc).val.toLinearMap.lTensor p.ResidueField) z := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c k => simp

theorem flat_residueField_bot : Module.Flat R (⊥ : Ideal R).ResidueField := by
  haveI : Module.Flat R (R ⧸ (⊥ : Ideal R)) :=
    Module.Flat.of_linearEquiv (Submodule.quotEquivOfEqBot (⊥ : Ideal R) rfl)
  haveI : Module.Flat (R ⧸ (⊥ : Ideal R)) (⊥ : Ideal R).ResidueField :=
    IsLocalization.flat _ (nonZeroDivisors (R ⧸ (⊥ : Ideal R)))
  exact Module.Flat.trans R (R ⧸ (⊥ : Ideal R)) _

theorem exists_one_tmul_eq {M : Type*} [AddCommGroup M] [Module R M] [p.IsMaximal]
    (z : p.ResidueField ⊗[R] M) : ∃ m : M, z = (1 : p.ResidueField) ⊗ₜ[R] m := by
  induction z with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨n, rfl⟩ := hy
    exact ⟨m + n, by simp [TensorProduct.tmul_add]⟩
  | tmul c m =>
    obtain ⟨r, rfl⟩ := p.algebraMap_residueField_surjective c
    refine ⟨r • m, ?_⟩
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]

theorem mem_smul_top_of_one_tmul_eq_zero {M : Type*} [AddCommGroup M] [Module R M] [p.IsMaximal]
    {m : M} (hm : (1 : p.ResidueField) ⊗ₜ[R] m = 0) : m ∈ p • (⊤ : Submodule R M) := by

  let e₁ : (R ⧸ p) ≃ₗ[R] p.ResidueField :=
    LinearEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField).toLinearMap
      p.bijective_algebraMap_quotient_residueField
  have h1 : (e₁.symm.rTensor M) ((1 : p.ResidueField) ⊗ₜ[R] m) = (1 : R ⧸ p) ⊗ₜ[R] m := by
    rw [LinearEquiv.rTensor_tmul]
    congr 1
    rw [LinearEquiv.symm_apply_eq]
    simp [e₁]
  have h2 : (1 : R ⧸ p) ⊗ₜ[R] m = 0 := by rw [← h1, hm, map_zero]
  have h3 := congrArg (TensorProduct.quotTensorEquivQuotSMul M p) h2
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero] at h3
  exact (Submodule.Quotient.mk_eq_zero _).1 h3

theorem φ_injective : Function.Injective (φ qc p) := by
  by_cases hp : p = ⊥
  · subst hp
    haveI := flat_residueField_bot (R := R)
    intro x y hxy
    rw [φ_apply_eq_lTensor, φ_apply_eq_lTensor] at hxy
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective hxy
  · haveI : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hp
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨k, rfl⟩ := exists_one_tmul_eq p z
    rw [φ_tmul] at hz
    have hk : (k : H) ∈ p • (⊤ : Submodule R H) := mem_smul_top_of_one_tmul_eq_zero p hz
    obtain ⟨t, rfl⟩ : ∃ t : R, p = Ideal.span {t} :=
      ⟨Submodule.IsPrincipal.generator p, (Ideal.span_singleton_generator p).symm⟩
    have ht : t ≠ 0 := by
      rintro rfl
      exact hp (by simp)
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hk
    obtain ⟨h', -, hh'⟩ := hk
    have hmem : h' ∈ hopfKer qc := mem_hopfKer_of_smul_mem qc ht (hh' ▸ k.2)
    have hk' : k = t • (⟨h', hmem⟩ : ↥(hopfKer qc)) := Subtype.ext (by simp [hh'])
    rw [hk', TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one,
      Ideal.algebraMap_residueField_eq_zero.2 (Ideal.mem_span_singleton_self t), TensorProduct.zero_tmul]

end Fibre

section FibreHopf

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {H : Type} [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
  [Coalgebra.IsCocomm R H]
variable {H' : Type} [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
variable (qc : H →ₐc[R] H') (p : Ideal R) [p.IsPrime]

noncomputable def Kκ : Subalgebra p.ResidueField (p.ResidueField ⊗[R] H) := (φ qc p).range

theorem tmul_coe_mem_Kκ (c : p.ResidueField) (k : ↥(hopfKer qc)) :
    c ⊗ₜ[R] (k : H) ∈ Kκ qc p := ⟨c ⊗ₜ[R] k, rfl⟩

theorem comul_mem_span_of_mem_Kκ {x : p.ResidueField ⊗[R] H} (hx : x ∈ Kκ qc p) :
    Coalgebra.comul (R := p.ResidueField) x ∈
      Submodule.span p.ResidueField
        {t : (p.ResidueField ⊗[R] H) ⊗[p.ResidueField] (p.ResidueField ⊗[R] H) |
          ∃ a ∈ Kκ qc p, ∃ b ∈ Kκ qc p, t = a ⊗ₜ[p.ResidueField] b} := by
  set W := Submodule.span p.ResidueField
        {t : (p.ResidueField ⊗[R] H) ⊗[p.ResidueField] (p.ResidueField ⊗[R] H) |
          ∃ a ∈ Kκ qc p, ∃ b ∈ Kκ qc p, t = a ⊗ₜ[p.ResidueField] b} with hW
  obtain ⟨z, rfl⟩ := hx
  induction z with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add]
    exact W.add_mem hx hy
  | tmul c k =>
    change Coalgebra.comul (R := p.ResidueField) (φ qc p (c ⊗ₜ[R] k)) ∈ W
    rw [φ_tmul, TensorProduct.comul_tmul, CommSemiring.comul_apply]
    obtain ⟨w, hw⟩ := HopfKerHopf.comul_coe_mem_range qc k
    rw [← hw]
    clear hw
    induction w with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, TensorProduct.tmul_add, map_add]
      exact W.add_mem hx hy
    | tmul a b =>
      rw [HopfKerHopf.ι₂_tmul, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
      exact Submodule.subset_span ⟨_, tmul_coe_mem_Kκ qc p 1 a, _, tmul_coe_mem_Kκ qc p c b, rfl⟩

theorem antipode_mem_Kκ {x : p.ResidueField ⊗[R] H} (hx : x ∈ Kκ qc p) :
    HopfAlgebra.antipode p.ResidueField x ∈ Kκ qc p := by
  obtain ⟨z, rfl⟩ := hx
  induction z with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add]
    exact (Kκ qc p).add_mem hx hy
  | tmul c k =>
    change HopfAlgebra.antipode p.ResidueField (φ qc p (c ⊗ₜ[R] k)) ∈ Kκ qc p
    rw [φ_tmul, TensorProduct.antipode_def, TensorProduct.AlgebraTensorModule.map_tmul,
      CommSemiring.antipode_eq_id, LinearMap.id_apply]
    exact tmul_coe_mem_Kκ qc p c ⟨_, HopfKerHopf.antipode_mem qc k.2⟩

theorem faithfullyFlat_Kκ : Module.FaithfullyFlat ↥(Kκ qc p) (p.ResidueField ⊗[R] H) :=
  HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem (Kκ qc p)
    (fun _ hx => comul_mem_span_of_mem_Kκ qc p hx) (fun _ hx => antipode_mem_Kκ qc p hx)

end FibreHopf

section Assembly

variable (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
  [Coalgebra.IsCocomm R H]
variable (H' : Type) [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
variable (qc : H →ₐc[R] H') (hqc : Function.Surjective qc)

theorem φ_flat (p : Ideal R) [p.IsPrime] : (φ qc p).toRingHom.Flat := by
  haveI := faithfullyFlat_Kκ qc p
  have h1 : (algebraMap ↥(Kκ qc p) (p.ResidueField ⊗[R] H)).Flat :=
    RingHom.flat_algebraMap_iff.2 inferInstance
  have h2 : ((φ qc p).rangeRestrict).toRingHom.Flat :=
    RingHom.Flat.of_bijective ⟨(φ qc p).injective_codRestrict _ _ |>.2 (φ_injective qc p),
      (φ qc p).rangeRestrict_surjective⟩
  have h3 := RingHom.Flat.comp h2 h1
  convert h3 using 1
  rfl

theorem flat_hopfKer_H : Module.Flat ↥(hopfKer qc) H :=
  Module.Flat.of_forall_flat_residueField_tensorProduct_of_isPrincipalIdealRing
    (R := R) (A := ↥(hopfKer qc)) (B := H) (fun p _ => φ_flat R H H' qc p)

theorem smul_top_ne_top {𝔪 : Ideal ↥(hopfKer qc)} (hm : 𝔪.IsMaximal) :
    𝔪 • (⊤ : Submodule ↥(hopfKer qc) H) ≠ ⊤ := by
  classical
  haveI hmp : 𝔪.IsPrime := hm.isPrime
  let p : Ideal R := 𝔪.comap (algebraMap R ↥(hopfKer qc))
  haveI hp : p.IsPrime := Ideal.comap_isPrime _ 𝔪

  set κ := p.ResidueField with hκ
  haveI hffκ := faithfullyFlat_Kκ qc p
  let E : κ ⊗[R] ↥(hopfKer qc) ≃ₐ[κ] ↥(Kκ qc p) :=
    AlgEquiv.ofBijective (φ qc p).rangeRestrict
      ⟨(φ qc p).injective_codRestrict _ _ |>.2 (φ_injective qc p), (φ qc p).rangeRestrict_surjective⟩
  let incl : ↥(hopfKer qc) →+* κ ⊗[R] ↥(hopfKer qc) :=
    (Algebra.TensorProduct.includeRight : ↥(hopfKer qc) →ₐ[R] κ ⊗[R] ↥(hopfKer qc)).toRingHom
  let ψ : ↥(hopfKer qc) →+* ↥(Kκ qc p) := E.toAlgHom.toRingHom.comp incl

  let f₁ : κ →ₐ[R] 𝔪.ResidueField := Ideal.ResidueField.mapₐ p 𝔪 (Algebra.ofId R ↥(hopfKer qc)) rfl
  let f₂ : ↥(hopfKer qc) →ₐ[R] 𝔪.ResidueField := IsScalarTower.toAlgHom R ↥(hopfKer qc) 𝔪.ResidueField
  let g : κ ⊗[R] ↥(hopfKer qc) →ₐ[R] 𝔪.ResidueField :=
    Algebra.TensorProduct.lift f₁ f₂ (fun _ _ => Commute.all _ _)
  let g' : ↥(Kκ qc p) →+* 𝔪.ResidueField := g.toRingHom.comp E.symm.toAlgHom.toRingHom
  have hker : 𝔪.map ψ ≤ RingHom.ker g' := by
    rw [Ideal.map_le_iff_le_comap]
    intro m hmm
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change g (E.symm (E (incl m))) = 0
    rw [AlgEquiv.symm_apply_apply]
    change g ((1 : κ) ⊗ₜ[R] m) = 0
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    change algebraMap ↥(hopfKer qc) 𝔪.ResidueField m = 0
    exact Ideal.algebraMap_residueField_eq_zero.2 hmm
  have hne : 𝔪.map ψ ≠ ⊤ := fun h =>
    (RingHom.ker_ne_top g') (top_le_iff.1 (h ▸ hker))
  obtain ⟨𝔫, h𝔫max, h𝔫⟩ := Ideal.exists_le_maximal _ hne
  have hff : 𝔫 • (⊤ : Submodule ↥(Kκ qc p) (κ ⊗[R] H)) ≠ ⊤ :=
    Module.FaithfullyFlat.submodule_ne_top h𝔫max

  intro htop
  apply hff
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] at htop ⊢
  have hj : (Algebra.TensorProduct.includeRight : H →ₐ[R] κ ⊗[R] H).toRingHom.comp (algebraMap ↥(hopfKer qc) H)
      = (algebraMap ↥(Kκ qc p) (κ ⊗[R] H)).comp ψ := by
    ext k
    rfl
  have h1 : (𝔪.map ψ).map (algebraMap ↥(Kκ qc p) (κ ⊗[R] H)) = ⊤ := by
    rw [Ideal.map_map, ← hj, ← Ideal.map_map, htop, Ideal.map_top]
  exact top_le_iff.1 (h1 ▸ Ideal.map_mono h𝔫)

end Assembly

end HopfAlgebra.FFHopfKerPID
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing.HopfAlgebra P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing.HopfAlgebra.FFHopfKerPID"
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing.HopfAlgebra"

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    (H' : Type) [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc) :
    Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) H := by
  haveI := HopfAlgebra.FFHopfKerPID.flat_hopfKer_H R H H' qc
  exact ⟨fun 𝔪 hm => HopfAlgebra.FFHopfKerPID.smul_top_ne_top R H H' qc hm⟩

end S_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing
end P2MW
export P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing (solution)
