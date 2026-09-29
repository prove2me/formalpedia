-- Prove2me | solution 1 for HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c00a474c-fdb2-54d1-affa-b27edde2da5b

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_isHopfGalois_iff_ker_le_span_of_surjective
import Theorems.Thm_HopfAlgebra_isHopfGalois_of_isCocomm_of_finiteType_of_surjective
import Theorems.Thm_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing
import Theorems.Thm_Algebra_FiniteType_of_faithfullyFlat_of_finitePresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open scoped TensorProduct
open Coalgebra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk coaction coaction_apply hopfKer mem_hopfKer_iff IsHopfGalois isHopfGalois_iff_ker_le_span_of_surjective isHopfGalois_of_isCocomm_of_finiteType_of_surjective faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing"
namespace QuotientPID
p2m_open "HopfAlgebra"

section GenericFibre

variable {R : Type} [CommRing R] [IsDomain R]
variable {H : Type} [CommRing H] [HopfAlgebra R H]
variable {H' : Type} [CommRing H'] [HopfAlgebra R H'] (qc : H →ₐc[R] H')
variable (F : Type) [Field F] [Algebra R F] [IsFractionRing R F]

def augSet : Set H := {a : H | a ∈ hopfKer qc ∧ counit (R := R) a = 0}

noncomputable def qcF : F ⊗[R] H →ₐc[F] F ⊗[R] H' :=
  Bialgebra.TensorProduct.map (BialgHom.id F F) qc

theorem qcF_tmul (f : F) (h : H) : qcF qc F (f ⊗ₜ[R] h) = f ⊗ₜ[R] qc h := rfl

theorem qcF_surjective (hqc : Function.Surjective qc) : Function.Surjective (qcF qc F) := by
  intro y
  induction y with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩
  | tmul f h' =>
    obtain ⟨h, rfl⟩ := hqc h'
    exact ⟨f ⊗ₜ[R] h, qcF_tmul qc F f h⟩

noncomputable def E : (F ⊗[R] H) ⊗[F] (F ⊗[R] H') ≃ₗ[F] F ⊗[R] (H ⊗[R] H') :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R F F (F ⊗[R] H) H').trans
    (TensorProduct.AlgebraTensorModule.assoc R R F F H H')

theorem E_tmul (f g : F) (x : H) (y : H') :
    E (R := R) F ((f ⊗ₜ[R] x) ⊗ₜ[F] (g ⊗ₜ[R] y)) = (g * f) ⊗ₜ[R] (x ⊗ₜ[R] y) := by
  simp [E, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, TensorProduct.AlgebraTensorModule.assoc_tmul,
    TensorProduct.smul_tmul', smul_eq_mul]

theorem E_map_tTT (z : H ⊗[R] H) :
    E (R := R) F (Algebra.TensorProduct.map (AlgHom.id F (F ⊗[R] H)) (qcF qc F : F ⊗[R] H →ₐ[F] F ⊗[R] H')
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R F R F F F H H
        (((1 : F) ⊗ₜ[F] (1 : F)) ⊗ₜ[R] z)))
      = (1 : F) ⊗ₜ[R] Algebra.TensorProduct.map (AlgHom.id R H) (qc : H →ₐ[R] H') z := by
  induction z with
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul x y =>
    rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply]
    change E F ((1 : F) ⊗ₜ[R] x ⊗ₜ[F] qcF qc F ((1 : F) ⊗ₜ[R] y)) = _
    rw [qcF_tmul, E_tmul, mul_one]
    rfl

theorem E_coaction_one_tmul (h : H) :
    E (R := R) F (coaction (qcF qc F) ((1 : F) ⊗ₜ[R] h)) = (1 : F) ⊗ₜ[R] coaction qc h := by
  rw [coaction_apply, coaction_apply, TensorProduct.comul_tmul]
  exact E_map_tTT qc F (comul (R := R) h)

theorem E_one_tmul_tmul_one (h : H) :
    E (R := R) F (((1 : F) ⊗ₜ[R] h) ⊗ₜ[F] (1 : F ⊗[R] H')) = (1 : F) ⊗ₜ[R] (h ⊗ₜ[R] (1 : H')) := by
  rw [Algebra.TensorProduct.one_def, E_tmul, mul_one]

variable [Module.Flat R H] [Module.Flat R H']

theorem mem_hopfKer_of_one_tmul_mem {h : H} (hh : (1 : F) ⊗ₜ[R] h ∈ hopfKer (qcF qc F)) : h ∈ hopfKer qc := by
  rw [mem_hopfKer_iff] at hh ⊢
  have h1 := congrArg (E (R := R) (H := H) (H' := H') F) hh
  rw [E_coaction_one_tmul, E_one_tmul_tmul_one, ← sub_eq_zero, ← TensorProduct.tmul_sub] at h1
  have h2 : (TensorProduct.mk R F (H ⊗[R] H') 1) (coaction qc h - h ⊗ₜ[R] 1) = 0 := h1
  rw [IsLocalizedModule.eq_zero_iff (nonZeroDivisors R) (TensorProduct.mk R F (H ⊗[R] H') 1)] at h2
  obtain ⟨s, hs⟩ := h2
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := H ⊗[R] H') s.2
  have : (s : R) • (coaction qc h - h ⊗ₜ[R] 1) = (s : R) • 0 := by rw [smul_zero]; exact hs
  exact sub_eq_zero.mp (hreg this)

theorem counit_one_tmul (h : H) :
    counit (R := F) ((1 : F) ⊗ₜ[R] h) = algebraMap R F (counit (R := R) h) := by
  simp [TensorProduct.counit_tmul, Algebra.algebraMap_eq_smul_one]

theorem span_augSet_qcF_le :
    Ideal.span (augSet (qcF qc F)) ≤ Ideal.span ((fun a : H => (1 : F) ⊗ₜ[R] a) '' augSet qc) := by
  refine Ideal.span_le.mpr ?_
  rintro w ⟨hw, hεw⟩
  obtain ⟨⟨h, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors R) (TensorProduct.mk R F H 1) w
  simp only [TensorProduct.mk_apply] at hs

  have hsw : (s : R) • w = (1 : F) ⊗ₜ[R] h := hs
  have hs0 : (algebraMap R F s) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hsw' : algebraMap R F s • w = (1 : F) ⊗ₜ[R] h := by rw [algebraMap_smul]; exact hsw

  have hmem : (1 : F) ⊗ₜ[R] h ∈ hopfKer (qcF qc F) := by
    rw [← hsw']; exact Subalgebra.smul_mem _ hw _
  have hε : counit (R := R) h = 0 := by
    have := congrArg (counit (R := F) (A := F ⊗[R] H)) hsw'
    rw [map_smul, hεw, smul_zero, counit_one_tmul] at this
    exact (IsFractionRing.injective R F) (by rw [map_zero]; exact this.symm)
  have hh : h ∈ augSet qc := ⟨mem_hopfKer_of_one_tmul_mem qc F hmem, hε⟩
  have hw_eq : w = (algebraMap R F s)⁻¹ • ((1 : F) ⊗ₜ[R] h) := by
    rw [← hsw', smul_smul, inv_mul_cancel₀ hs0, one_smul]
  rw [hw_eq]
  exact Submodule.smul_of_tower_mem _ _ (Ideal.subset_span ⟨h, hh, rfl⟩)

theorem exists_smul_eq_one_tmul_of_mem_span {z : F ⊗[R] H}
    (hz : z ∈ Ideal.span ((fun a : H => (1 : F) ⊗ₜ[R] a) '' augSet qc)) :
    ∃ s : R, s ≠ 0 ∧ ∃ j ∈ Ideal.span (augSet qc), s • z = (1 : F) ⊗ₜ[R] j := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨1, one_ne_zero, a, Ideal.subset_span ha, by rw [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, 0, Ideal.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, j, hj, hsx⟩ := hx
    obtain ⟨t, ht, l, hl, hty⟩ := hy
    refine ⟨s * t, mul_ne_zero hs ht, t • j + s • l, Ideal.add_mem _ (Submodule.smul_of_tower_mem _ _ hj)
      (Submodule.smul_of_tower_mem _ _ hl), ?_⟩
    have e1 : (s * t) • x = t • (s • x) := by rw [mul_comm, mul_smul]
    have e2 : (s * t) • y = s • (t • y) := by rw [mul_smul]
    rw [smul_add, e1, e2, hsx, hty, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul]
  | smul t x _ hx =>
    obtain ⟨s, hs, j, hj, hsx⟩ := hx
    obtain ⟨⟨h, u⟩, hu⟩ := IsLocalizedModule.surj (nonZeroDivisors R) (TensorProduct.mk R F H 1) t
    simp only [TensorProduct.mk_apply] at hu
    have hu' : (u : R) • t = (1 : F) ⊗ₜ[R] h := hu
    refine ⟨u * s, mul_ne_zero (nonZeroDivisors.ne_zero u.2) hs, h * j, Ideal.mul_mem_left _ _ hj, ?_⟩
    have e : ((u : R) • t) * (s • x) = ((u : R) * s) • (t • x) := by
      rw [smul_eq_mul t x, smul_mul_assoc, mul_smul_comm, mul_smul]
    rw [← e, hu', hsx, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem exists_smul_mem_span_augSet (hqc : Function.Surjective qc) (hgen : IsHopfGalois (qcF qc F))
    {i : H} (hi : qc i = 0) :
    ∃ s : R, s ≠ 0 ∧ s • i ∈ Ideal.span (augSet qc) := by
  have hker : RingHom.ker (qcF qc F : F ⊗[R] H →ₐ[F] F ⊗[R] H') ≤ Ideal.span (augSet (qcF qc F)) :=
    (HopfAlgebra.isHopfGalois_iff_ker_le_span_of_surjective (qcF qc F) (qcF_surjective qc F hqc)).mp hgen
  have h1 : (1 : F) ⊗ₜ[R] i ∈ RingHom.ker (qcF qc F : F ⊗[R] H →ₐ[F] F ⊗[R] H') := by
    rw [RingHom.mem_ker]
    change qcF qc F ((1 : F) ⊗ₜ[R] i) = 0
    rw [qcF_tmul, hi, TensorProduct.tmul_zero]
  have h2 := span_augSet_qcF_le qc F (hker h1)
  obtain ⟨s, hs, j, hj, hsj⟩ := exists_smul_eq_one_tmul_of_mem_span qc F h2
  refine ⟨s, hs, ?_⟩

  have h3 : (TensorProduct.mk R F H 1) (s • i - j) = 0 := by
    rw [TensorProduct.mk_apply, TensorProduct.tmul_sub, TensorProduct.tmul_smul, hsj, sub_self]
  rw [IsLocalizedModule.eq_zero_iff (nonZeroDivisors R) (TensorProduct.mk R F H 1)] at h3
  obtain ⟨u, hu⟩ := h3
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := H) u.2
  have : (u : R) • (s • i - j) = (u : R) • 0 := by rw [smul_zero]; exact hu
  have h4 : s • i = j := sub_eq_zero.mp (hreg this)
  rw [h4]; exact hj

end GenericFibre

section TorsionFreeGeneral

variable {R : Type} [CommRing R] [IsDomain R]
variable {K : Type} [CommRing K] [Algebra R K] (ε : K →ₐ[R] R)
variable {M : Type} [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower R K M]

theorem exact_subtype_smul_mkQ {r : R} (hr : r ≠ 0) :
    Function.Exact (Submodule.subtype (RingHom.ker ε))
      ((algebraMap R K r) • (Submodule.mkQ (RingHom.ker ε) : K →ₗ[K] K ⧸ RingHom.ker ε)) := by
  intro x
  rw [LinearMap.smul_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    Submodule.coe_subtype, Subtype.range_coe_subtype, Set.mem_setOf_eq, RingHom.mem_ker,
    RingHom.mem_ker, smul_eq_mul, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_eq_zero]
  exact ⟨fun h => h.resolve_left hr, fun h => Or.inr h⟩

variable [Module.Flat K M]

theorem mem_smul_top_of_smul_mem {r : R} (hr : r ≠ 0) {y : M}
    (hy : r • y ∈ ((RingHom.ker ε) • ⊤ : Submodule K M)) : y ∈ ((RingHom.ker ε) • ⊤ : Submodule K M) := by
  set 𝔨 : Ideal K := RingHom.ker ε
  set φ : K →ₗ[K] K ⧸ 𝔨 := (algebraMap R K r) • (Submodule.mkQ 𝔨 : K →ₗ[K] K ⧸ 𝔨)
  have hex := Module.Flat.lTensor_exact M (exact_subtype_smul_mkQ ε hr)

  have hzero : ∀ z ∈ (𝔨 • ⊤ : Submodule K M), z ⊗ₜ[K] (Submodule.Quotient.mk (p := 𝔨) (1 : K)) = 0 := by
    intro z hz
    refine Submodule.smul_induction_on hz (fun k hk m _ => ?_) (fun x y hx hy => ?_)
    · rw [TensorProduct.smul_tmul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
        (Submodule.Quotient.mk_eq_zero 𝔨).mpr hk, TensorProduct.tmul_zero]
    · rw [TensorProduct.add_tmul, hx, hy, add_zero]
  have h1 : (φ.lTensor M) (y ⊗ₜ[K] (1 : K)) = 0 := by
    rw [LinearMap.lTensor_tmul, LinearMap.smul_apply, Submodule.mkQ_apply, ← TensorProduct.smul_tmul,
      algebraMap_smul]
    exact hzero _ hy
  have h2 : y ⊗ₜ[K] (1 : K) ∈ LinearMap.range ((Submodule.subtype 𝔨).lTensor M) := by
    rw [LinearMap.exact_iff] at hex
    rw [← hex, LinearMap.mem_ker]; exact h1
  obtain ⟨w, hw⟩ := h2
  have h3 : ∀ w : M ⊗[K] ↥𝔨, TensorProduct.rid K M ((Submodule.subtype 𝔨).lTensor M w) ∈ (𝔨 • ⊤ : Submodule K M) := by
    intro w
    induction w with
    | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
    | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
    | tmul m k =>
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, TensorProduct.rid_tmul]
      exact Submodule.smul_mem_smul k.2 Submodule.mem_top
  have h4 : y = TensorProduct.rid K M ((Submodule.subtype 𝔨).lTensor M w) := by
    rw [hw, TensorProduct.rid_tmul, one_smul]
  rw [h4]; exact h3 w

end TorsionFreeGeneral

section TorsionFree

variable {R : Type} [CommRing R] [IsDomain R]
variable {H : Type} [CommRing H] [HopfAlgebra R H]
variable {H' : Type} [CommRing H'] [HopfAlgebra R H'] (qc : H →ₐc[R] H')

noncomputable def epsK : ↥(hopfKer qc) →ₐ[R] R := (Bialgebra.counitAlgHom R H).comp (hopfKer qc).val

theorem epsK_apply (k : ↥(hopfKer qc)) : epsK qc k = counit (R := R) (k : H) := rfl

theorem span_augSet_eq_map :
    Ideal.span (augSet qc) = (RingHom.ker (epsK qc)).map (algebraMap ↥(hopfKer qc) H) := by
  change Ideal.span (augSet qc) = Ideal.span _
  congr 1
  ext a
  constructor
  · rintro ⟨ha, hε⟩
    exact ⟨⟨a, ha⟩, by simpa [RingHom.mem_ker, epsK_apply] using hε, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, by simpa [RingHom.mem_ker, epsK_apply] using hk⟩

set_option synthInstance.maxHeartbeats 1600000 in

theorem mem_span_augSet_of_smul_mem [Module.Flat ↥(hopfKer qc) H] {r : R} (hr : r ≠ 0) {y : H}
    (hy : r • y ∈ Ideal.span (augSet qc)) : y ∈ Ideal.span (augSet qc) := by
  have hmem : ∀ z : H, z ∈ Ideal.span (augSet qc) ↔
      z ∈ ((RingHom.ker (epsK qc)) • ⊤ : Submodule ↥(hopfKer qc) H) := by
    intro z
    rw [span_augSet_eq_map, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
  rw [hmem] at hy ⊢
  exact mem_smul_top_of_smul_mem (epsK qc) hr hy

end TorsionFree

section Descent

theorem isNoetherianRing_of_faithfullyFlat (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] [IsNoetherianRing B] : IsNoetherianRing A := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  exact Ideal.FG.of_FG_map_of_faithfullyFlat (S := B) (IsNoetherian.noetherian _)

end Descent

end HopfAlgebra.QuotientPID

open _root_.HopfAlgebra _root_.P2MW.S_HopfAlgebra_isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective.HopfAlgebra HopfAlgebra.QuotientPID in
theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    (H' : Type) [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc) :
    HopfAlgebra.IsHopfGalois qc ∧
      Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) H ∧
      Algebra.FiniteType R ↥(HopfAlgebra.hopfKer qc) := by

  haveI hFF : Module.FaithfullyFlat ↥(hopfKer qc) H :=
    HopfAlgebra.faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing R H H' qc hqc

  let F : Type := FractionRing R
  have hgen : IsHopfGalois (qcF qc F) :=
    HopfAlgebra.isHopfGalois_of_isCocomm_of_finiteType_of_surjective F (F ⊗[R] H) (F ⊗[R] H') (qcF qc F)
      (qcF_surjective qc F hqc)

  have hle : RingHom.ker (qc : H →ₐ[R] H') ≤ Ideal.span (augSet qc) := by
    intro i hi
    obtain ⟨s, hs, hsi⟩ := exists_smul_mem_span_augSet qc F hqc hgen (i := i) hi
    exact mem_span_augSet_of_smul_mem qc hs hsi
  have hHG : IsHopfGalois qc := (HopfAlgebra.isHopfGalois_iff_ker_le_span_of_surjective qc hqc).mpr hle
  refine ⟨hHG, hFF, ?_⟩

  haveI : IsNoetherianRing R := inferInstance
  haveI : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing R H
  haveI : IsNoetherianRing ↥(hopfKer qc) := isNoetherianRing_of_faithfullyFlat ↥(hopfKer qc) H
  haveI : Algebra.FiniteType ↥(hopfKer qc) H := Algebra.FiniteType.of_restrictScalars_finiteType R _ H
  haveI : Algebra.FinitePresentation ↥(hopfKer qc) H := (Algebra.FinitePresentation.of_finiteType).mp ‹_›
  exact Algebra.FiniteType.of_faithfullyFlat_of_finitePresentation R ↥(hopfKer qc) H

end S_HopfAlgebra_isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective
end P2MW
export P2MW.S_HopfAlgebra_isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective (solution)
