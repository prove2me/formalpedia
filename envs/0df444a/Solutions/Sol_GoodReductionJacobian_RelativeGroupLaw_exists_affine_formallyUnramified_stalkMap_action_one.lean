-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_affine_formallyUnramified_stalkMap_action_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/7b15c09f-9842-5315-9ecc-5975618779d9

import Mathlib
import Theorems.Thm_Algebra_FormallySmooth_etale_aeval_of_basis_kaehlerDifferential
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq
import Theorems.Thm_AlgebraicGeometry_maximalIdeal_stalk_pullback_le_of_sections
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_affine_formallyUnramified_stalkMap_action_one

set_option autoImplicit false

universe u

open scoped TensorProduct
open KaehlerDifferential

namespace CutAlg

theorem det_basis_baseChange_tmul
    {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A M) (x : ι → M)
    (A' : Type u) [CommRing A'] [Algebra A A'] :
    (Algebra.TensorProduct.basis A' b).det (fun i => (1 : A') ⊗ₜ[A] x i) = algebraMap A A' (b.det x) := by
  classical
  have hmat : (Algebra.TensorProduct.basis A' b).toMatrix (fun i => (1 : A') ⊗ₜ[A] x i) =
      (b.toMatrix x).map (algebraMap A A') := by
    ext i j
    simp [Module.Basis.toMatrix_apply, Algebra.TensorProduct.basis_repr_tmul]
  rw [Module.Basis.det_apply, Module.Basis.det_apply, hmat, RingHom.map_det, RingHom.mapMatrix_apply]

theorem algebraMap_det_ne_zero_of_linearIndependent
    {A : Type u} [CommRing A] {K : Type u} [Field K] [Algebra A K] {M : Type u} [AddCommGroup M] [Module A M]
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A M) (x : ι → M)
    (hx : LinearIndependent K (fun i => (1 : K) ⊗ₜ[A] x i : ι → K ⊗[A] M)) :
    algebraMap A K (b.det x) ≠ 0 := by
  classical
  rw [← det_basis_baseChange_tmul b x K]
  cases isEmpty_or_nonempty ι with
  | inl _ => rw [Module.Basis.det_apply, Matrix.det_isEmpty]; exact one_ne_zero
  | inr _ =>
  have hcard : Fintype.card ι = Module.finrank K (K ⊗[A] M) :=
    (Module.finrank_eq_card_basis (Algebra.TensorProduct.basis K b)).symm
  let B := basisOfLinearIndependentOfCardEqFinrank hx hcard
  have hB : (⇑B : ι → K ⊗[A] M) = fun i => (1 : K) ⊗ₜ[A] x i := coe_basisOfLinearIndependentOfCardEqFinrank hx hcard
  have hu := (Algebra.TensorProduct.basis K b).isUnit_det B
  rw [hB] at hu
  exact hu.ne_zero

theorem exists_basis_baseChange_of_isUnit_det
    {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A M) (x : ι → M)
    (A' : Type u) [CommRing A'] [Algebra A A'] (hu : IsUnit (algebraMap A A' (b.det x))) :
    ∃ b' : Module.Basis ι A' (A' ⊗[A] M), ∀ i, b' i = (1 : A') ⊗ₜ[A] x i := by
  classical
  rw [← det_basis_baseChange_tmul b x A'] at hu
  obtain ⟨hli, hsp⟩ := (Algebra.TensorProduct.basis A' b).is_basis_iff_det.mpr hu
  exact ⟨Module.Basis.mk hli hsp.ge, fun i => by simp⟩

theorem exists_basis_kaehler_of_isLocalization
    {k : Type u} [CommRing k] {A A' : Type u} [CommRing A] [CommRing A'] [Algebra k A] [Algebra k A'] [Algebra A A']
    [IsScalarTower k A A'] (M : Submonoid A) [IsLocalization M A']
    {ι : Type} (x : ι → A) (b : Module.Basis ι A' (A' ⊗[A] Ω[A⁄k])) (hb : ∀ i, b i = (1 : A') ⊗ₜ[A] D k A (x i)) :
    ∃ b' : Module.Basis ι A' (Ω[A'⁄k]), ∀ i, b' i = D k A' (algebraMap A A' (x i)) := by
  haveI : Algebra.FormallyEtale A A' := Algebra.FormallyEtale.of_isLocalization (Rₘ := A') M
  refine ⟨b.map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A A'), fun i ↦ ?_⟩
  rw [Module.Basis.map_apply, hb, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    mapBaseChange_tmul, one_smul, map_D]

theorem nonempty_basis_kaehler_of_isStandardSmoothOfRelativeDimension
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    Nonempty (Module.Basis (Fin n) S (Ω[S⁄R])) := by
  classical
  obtain ⟨ι, σ, _, _, P, hP⟩ := (‹Algebra.IsStandardSmoothOfRelativeDimension n R S›).out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hcard : Fintype.card ((Set.range P.map)ᶜ : Set ι) = n := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP, Algebra.Presentation.dimension,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact ⟨P.basisKaehler.reindex (Fintype.equivFinOfCardEq hcard)⟩

section point

variable {k : Type u} [Field k] {P : Type u} [CommRing P] [Algebra k P] [Algebra P k] [IsScalarTower k P k]

lemma algebraMap_point_surjective : Function.Surjective (algebraMap P k) := fun c ↦
  ⟨algebraMap k P c, by rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]⟩

lemma algebraMap_algebraMap_point (c : k) : algebraMap P k (algebraMap k P c) = c := by
  rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

lemma one_tmul_smul (p : P) (ω : Ω[P⁄k]) :
    (1 : k) ⊗ₜ[P] (p • ω) = algebraMap P k p • ((1 : k) ⊗ₜ[P] ω) := by
  rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

lemma one_tmul_D_algebraMap_mul (c : k) (a : P) :
    (1 : k) ⊗ₜ[P] D k P (algebraMap k P c * a) = c • ((1 : k) ⊗ₜ[P] D k P a) := by
  rw [Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero, one_tmul_smul,
    algebraMap_algebraMap_point]

lemma tmul_eq_one_tmul_smul (c : k) (ω : Ω[P⁄k]) :
    c ⊗ₜ[P] ω = (1 : k) ⊗ₜ[P] (algebraMap k P c • ω) := by
  rw [one_tmul_smul, algebraMap_algebraMap_point, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem kerCotangentToTensor_injective :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor k P k) := by
  have hf : Function.Surjective (algebraMap P k) := algebraMap_point_surjective
  let g : k →ₐ[k] P ⧸ (RingHom.ker (algebraMap P k) ^ 2) := Algebra.ofId k _
  have hg : (IsScalarTower.toAlgHom k P k).kerSquareLift.comp g = AlgHom.id k k := Subsingleton.elim _ _
  obtain ⟨l, hl⟩ := (retractionKerCotangentToTensorEquivSection (R := k) (P := P) (S := k) hf).symm ⟨g, hg⟩
  exact Function.LeftInverse.injective (g := l) fun x ↦ LinearMap.congr_fun hl x

lemma exists_eq_one_tmul_D (v : k ⊗[P] Ω[P⁄k]) :
    ∃ a : P, algebraMap P k a = 0 ∧ v = (1 : k) ⊗ₜ[P] D k P a := by

  have key : ∀ ω : Ω[P⁄k], ∃ a : P, (1 : k) ⊗ₜ[P] ω = (1 : k) ⊗ₜ[P] D k P a := by
    intro ω
    have hω : ω ∈ Submodule.span P (Set.range (D k P)) := by
      rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
    induction hω using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact ⟨a, rfl⟩
    | zero => exact ⟨0, by rw [map_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [TensorProduct.tmul_add, ha, hb, map_add, TensorProduct.tmul_add]⟩
    | smul p x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨algebraMap k P (algebraMap P k p) * a, ?_⟩
      rw [one_tmul_smul, ha, one_tmul_D_algebraMap_mul]

  have norm : ∀ a : P, ∃ a' : P, algebraMap P k a' = 0 ∧ (1 : k) ⊗ₜ[P] D k P a = (1 : k) ⊗ₜ[P] D k P a' := by
    intro a
    refine ⟨a - algebraMap k P (algebraMap P k a), ?_, ?_⟩
    · rw [map_sub, algebraMap_algebraMap_point, sub_self]
    · rw [map_sub, Derivation.map_algebraMap, sub_zero]
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero], by rw [map_zero, TensorProduct.tmul_zero]⟩
  | tmul c ω =>
    obtain ⟨a, ha⟩ := key (algebraMap k P c • ω)
    obtain ⟨a', ha'0, ha'⟩ := norm a
    exact ⟨a', ha'0, by rw [tmul_eq_one_tmul_smul, ha, ha']⟩
  | add x y hx hy =>
    obtain ⟨a, ha0, rfl⟩ := hx; obtain ⟨b, hb0, rfl⟩ := hy
    exact ⟨a + b, by rw [map_add, ha0, hb0, add_zero], by rw [map_add, TensorProduct.tmul_add]⟩

lemma one_tmul_D_eq_zero_of_mem_sq {c : P} (hc : c ∈ RingHom.ker (algebraMap P k) ^ 2) :
    (1 : k) ⊗ₜ[P] D k P c = 0 := by
  have hc1 : c ∈ RingHom.ker (algebraMap P k) := Ideal.pow_le_self two_ne_zero hc
  have h0 : Ideal.toCotangent _ (⟨c, hc1⟩ : RingHom.ker (algebraMap P k)) = 0 :=
    LinearMap.mem_ker.mp ((Ideal.mem_toCotangent_ker _).mpr hc)
  have := congrArg (kerCotangentToTensor k P k) h0
  rwa [kerCotangentToTensor_toCotangent, map_zero] at this

theorem ker_le_span_sup_sq (s : Set P) (hs : ∀ x ∈ s, algebraMap P k x = 0)
    (hsp : Submodule.span k ((fun a : P => (1 : k) ⊗ₜ[P] D k P a) '' s) = ⊤) :
    RingHom.ker (algebraMap P k) ≤ Ideal.span s ⊔ RingHom.ker (algebraMap P k) ^ 2 := by
  classical
  intro x hx
  have hmem : (1 : k) ⊗ₜ[P] D k P x ∈ Submodule.span k ((fun a : P => (1 : k) ⊗ₜ[P] D k P a) '' s) := by
    rw [hsp]; exact Submodule.mem_top
  rw [Submodule.mem_span_image_iff_exists_fun] at hmem
  obtain ⟨t, ht, c, hc⟩ := hmem

  set z : P := ∑ i : t, algebraMap k P (c i) * (i : P) with hz
  have hzs : z ∈ Ideal.span s :=
    Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span (ht i.2))
  have hz0 : algebraMap P k z = 0 := by
    rw [hz, map_sum]
    exact Finset.sum_eq_zero fun i _ ↦ by rw [map_mul, hs _ (ht i.2), mul_zero]
  have hy : x - z ∈ RingHom.ker (algebraMap P k) := by
    rw [RingHom.mem_ker, map_sub, hz0, sub_zero]; exact hx
  have hDz : (1 : k) ⊗ₜ[P] D k P z = (1 : k) ⊗ₜ[P] D k P x := by
    rw [← hc, hz, map_sum, TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ one_tmul_D_algebraMap_mul (c i) (i : P)
  have hker : kerCotangentToTensor k P k (Ideal.toCotangent _ ⟨x - z, hy⟩) = 0 := by
    rw [kerCotangentToTensor_toCotangent, map_sub, TensorProduct.tmul_sub, hDz, sub_self]
  rw [← map_zero (kerCotangentToTensor k P k)] at hker
  have h0 := kerCotangentToTensor_injective hker
  have hy2 : ((⟨x - z, hy⟩ : RingHom.ker (algebraMap P k)) : P) ∈ RingHom.ker (algebraMap P k) ^ 2 :=
    (Ideal.mem_toCotangent_ker _).mp (LinearMap.mem_ker.mpr h0)
  have : x = z + (x - z) := by ring
  rw [this]
  exact Submodule.add_mem_sup hzs hy2

end point

section adapted

variable {k : Type u} [Field k] {P Q : Type u} [CommRing P] [CommRing Q]
    [Algebra k P] [Algebra k Q] [Algebra P Q] [IsScalarTower k P Q]
    [Algebra Q k] [Algebra P k] [IsScalarTower P Q k] [IsScalarTower k Q k] [IsScalarTower k P k]

noncomputable def cotangentMap : k ⊗[P] Ω[P⁄k] →ₗ[k] k ⊗[Q] Ω[Q⁄k] :=
  ((KaehlerDifferential.mapBaseChange k P Q).baseChange k) ∘ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange P Q k k Ω[P⁄k]).symm.toLinearMap

lemma cotangentMap_one_tmul_D (a : P) :
    cotangentMap (k := k) (P := P) (Q := Q) ((1 : k) ⊗ₜ[P] D k P a) = (1 : k) ⊗ₜ[Q] D k Q (algebraMap P Q a) := by
  simp only [cotangentMap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]

end adapted

theorem exists_adapted_coords
    {k : Type u} [Field k] {P Q : Type u} [CommRing P] [CommRing Q]
    [Algebra k P] [Algebra k Q] [Algebra P Q] [IsScalarTower k P Q]
    [Algebra Q k] [Algebra P k] [IsScalarTower P Q k] [IsScalarTower k Q k] [IsScalarTower k P k]
    (hPQ : Function.Surjective (algebraMap P Q)) {g h : ℕ}
    (bP : Module.Basis (Fin g) k (k ⊗[P] Ω[P⁄k])) (bQ : Module.Basis (Fin h) k (k ⊗[Q] Ω[Q⁄k])) :
    h ≤ g ∧ ∃ (t : Fin h → P) (u : Fin (g - h) → P),
      (∀ i, algebraMap P k (t i) = 0) ∧ (∀ j, algebraMap P Q (u j) = 0) ∧
      ∃ b : Module.Basis (Fin h ⊕ Fin (g - h)) k (k ⊗[P] Ω[P⁄k]),
        (∀ i, b (Sum.inl i) = (1 : k) ⊗ₜ[P] D k P (t i)) ∧
        (∀ j, b (Sum.inr j) = (1 : k) ⊗ₜ[P] D k P (u j)) := by
  classical
  set V := k ⊗[P] Ω[P⁄k] with hV
  let I : Ideal P := RingHom.ker (algebraMap P Q)
  let φ : V →ₗ[k] k ⊗[Q] Ω[Q⁄k] := cotangentMap
  haveI : Module.Finite k V := Module.Finite.of_basis bP
  haveI : Module.Finite k (k ⊗[Q] Ω[Q⁄k]) := Module.Finite.of_basis bQ
  have hεPQ : ∀ a : P, algebraMap Q k (algebraMap P Q a) = algebraMap P k a := fun a ↦
    (IsScalarTower.algebraMap_apply P Q k a).symm

  let W : Submodule k V := Submodule.span k ((fun a : P ↦ (1 : k) ⊗ₜ[P] D k P a) '' (I : Set P))
  have hWmem : ∀ w ∈ W, ∃ a ∈ I, w = (1 : k) ⊗ₜ[P] D k P a := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨a, ha, rfl⟩ := hx; exact ⟨a, ha, rfl⟩
    | zero => exact ⟨0, I.zero_mem, by rw [map_zero, TensorProduct.tmul_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx; obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, I.add_mem ha hb, by rw [map_add, TensorProduct.tmul_add]⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨algebraMap k P c * a, I.mul_mem_left _ ha, (one_tmul_D_algebraMap_mul c a).symm⟩
  have hφ : ∀ a : P, φ ((1 : k) ⊗ₜ[P] D k P a) = (1 : k) ⊗ₜ[Q] D k Q (algebraMap P Q a) :=
    cotangentMap_one_tmul_D
  have hker : LinearMap.ker φ = W := by
    apply le_antisymm
    · intro v hv
      obtain ⟨a, ha0, rfl⟩ := exists_eq_one_tmul_D v
      rw [LinearMap.mem_ker, hφ] at hv

      have hb : algebraMap P Q a ∈ RingHom.ker (algebraMap Q k) := by
        rw [RingHom.mem_ker, hεPQ, ha0]
      have hb2 : algebraMap P Q a ∈ RingHom.ker (algebraMap Q k) ^ 2 := by
        have h0 : kerCotangentToTensor k Q k (Ideal.toCotangent _ ⟨_, hb⟩) = 0 := by
          rw [kerCotangentToTensor_toCotangent]; exact hv
        rw [← map_zero (kerCotangentToTensor k Q k)] at h0
        exact (Ideal.mem_toCotangent_ker _).mp (LinearMap.mem_ker.mpr (kerCotangentToTensor_injective h0))
      have hmap : RingHom.ker (algebraMap Q k) = (RingHom.ker (algebraMap P k)).map (algebraMap P Q) := by
        have : RingHom.ker (algebraMap P k) = (RingHom.ker (algebraMap Q k)).comap (algebraMap P Q) := by
          ext x; simp only [RingHom.mem_ker, Ideal.mem_comap, hεPQ]
        rw [this, Ideal.map_comap_of_surjective _ hPQ]
      rw [hmap, ← Ideal.map_pow] at hb2
      obtain ⟨c, hc, hca⟩ := (Ideal.mem_map_iff_of_surjective _ hPQ).mp hb2
      have haI : a - c ∈ I := by
        change a - c ∈ RingHom.ker (algebraMap P Q)
        rw [RingHom.mem_ker, map_sub, hca, sub_self]
      have : (1 : k) ⊗ₜ[P] D k P a = (1 : k) ⊗ₜ[P] D k P (a - c) + (1 : k) ⊗ₜ[P] D k P c := by
        rw [map_sub, TensorProduct.tmul_sub, sub_add_cancel]
      rw [this, one_tmul_D_eq_zero_of_mem_sq hc, add_zero]
      exact Submodule.subset_span ⟨a - c, haI, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hφ, RingHom.mem_ker.mp ha, map_zero, TensorProduct.tmul_zero]

  have hsurj : LinearMap.range φ = ⊤ := by
    rw [eq_top_iff]
    rintro v -
    obtain ⟨b, -, rfl⟩ := exists_eq_one_tmul_D v
    obtain ⟨a, rfl⟩ := hPQ b
    exact ⟨(1 : k) ⊗ₜ[P] D k P a, hφ a⟩
  have hdimV : Module.finrank k V = g := by rw [Module.finrank_eq_card_basis bP, Fintype.card_fin]
  have hdimQ : Module.finrank k (k ⊗[Q] Ω[Q⁄k]) = h := by rw [Module.finrank_eq_card_basis bQ, Fintype.card_fin]
  have hrk := LinearMap.finrank_range_add_finrank_ker φ
  rw [hsurj, finrank_top, hdimQ, hdimV, hker] at hrk
  have hhg : h ≤ g := by omega
  have hdimW : Module.finrank k W = g - h := by omega
  refine ⟨hhg, ?_⟩

  haveI : Module.Free k W := Module.Free.of_divisionRing k W
  let bW : Module.Basis (Fin (g - h)) k W := Module.finBasisOfFinrankEq k W hdimW
  choose u huI hu using fun j ↦ hWmem (bW j) (bW j).2

  let uvec : Fin (g - h) → V := fun j ↦ (bW j : V)
  have hli : LinearIndependent k uvec :=
    (LinearIndependent.map' (R := k) (M := ↥W) (M' := V) bW.linearIndependent W.subtype
      (Submodule.ker_subtype W) :)
  let b₀ := Module.Basis.sumExtend hli
  have hb₀inl : ∀ j, b₀ (Sum.inl j) = uvec j := by
    intro j
    simp only [b₀, Module.Basis.sumExtend, Module.Basis.reindex_apply, Equiv.symm_symm,
      Module.Basis.extend_apply_self]
    simp only [Trans.trans]
    erw [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.Set.sumDiffSubset_apply_inl]
    rfl
  haveI : Finite (Fin (g - h) ⊕ ↑(Module.Basis.sumExtendIndex hli)) := Module.Finite.finite_basis b₀
  haveI : Finite ↑(Module.Basis.sumExtendIndex hli) :=
    Finite.of_injective (Sum.inr : _ → Fin (g - h) ⊕ ↑(Module.Basis.sumExtendIndex hli)) Sum.inr_injective
  letI : Fintype ↑(Module.Basis.sumExtendIndex hli) := Fintype.ofFinite _
  have hcardC : Fintype.card ↑(Module.Basis.sumExtendIndex hli) = h := by
    have := Module.finrank_eq_card_basis b₀
    rw [hdimV, Fintype.card_sum, Fintype.card_fin] at this
    omega
  let eC : ↑(Module.Basis.sumExtendIndex hli) ≃ Fin h := Fintype.equivFinOfCardEq hcardC
  let b : Module.Basis (Fin h ⊕ Fin (g - h)) k V :=
    b₀.reindex ((Equiv.sumCongr (Equiv.refl _) eC).trans (Equiv.sumComm _ _))
  have hbinl : ∀ i, b (Sum.inl i) = b₀ (Sum.inr (eC.symm i)) := fun i ↦ by
    simp [b, Module.Basis.reindex_apply]
  have hbinr : ∀ j, b (Sum.inr j) = uvec j := fun j ↦ by
    simp [b, Module.Basis.reindex_apply, hb₀inl]
  choose t ht0 ht using fun i ↦ exists_eq_one_tmul_D (b (Sum.inl i))
  refine ⟨t, u, ht0, fun j ↦ (RingHom.mem_ker.mp (huI j)), b, ht, fun j ↦ ?_⟩
  rw [hbinr]
  exact hu j

section localization

variable {k : Type u} [Field k] {A P : Type u} [CommRing A] [CommRing P]
    [Algebra k A] [Algebra k P] [Algebra A P] [IsScalarTower k A P]
    [Algebra P k] [Algebra A k] [IsScalarTower A P k]

noncomputable def cotangentEquivOfFormallyEtale [Algebra.FormallyEtale A P] :
    k ⊗[A] Ω[A⁄k] ≃ₗ[k] k ⊗[P] Ω[P⁄k] :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange A P k k Ω[A⁄k]).symm ≪≫ₗ
    LinearEquiv.baseChange P k _ _ (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A P)

lemma cotangentEquivOfFormallyEtale_one_tmul_D [Algebra.FormallyEtale A P] (a : A) :
    cotangentEquivOfFormallyEtale (k := k) (A := A) (P := P) ((1 : k) ⊗ₜ[A] D k A a) =
      (1 : k) ⊗ₜ[P] D k P (algebraMap A P a) := by
  simp only [cotangentEquivOfFormallyEtale, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
  change LinearMap.baseChange k (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A P).toLinearMap
    ((1 : k) ⊗ₜ[P] ((1 : P) ⊗ₜ[A] D k A a)) = _
  rw [LinearMap.baseChange_tmul, LinearEquiv.coe_toLinearMap,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, map_D]

end localization

theorem exists_coords_of_isLocalization
    {k : Type u} [Field k] {A P : Type u} [CommRing A] [CommRing P]
    [Algebra k A] [Algebra k P] [Algebra A P] [IsScalarTower k A P]
    [Algebra P k] [Algebra A k] [IsScalarTower A P k] [IsScalarTower k P k] [IsScalarTower k A k]
    (M : Submonoid A) [IsLocalization M P] (hM : ∀ s ∈ M, algebraMap A k s ≠ 0)
    {ι : Type} [Finite ι] (x : ι → P) (hx : ∀ l, algebraMap P k (x l) = 0)
    (b : Module.Basis ι k (k ⊗[P] Ω[P⁄k])) (hb : ∀ l, b l = (1 : k) ⊗ₜ[P] D k P (x l)) :
    ∃ (a : ι → A) (s : ι → A), (∀ l, s l ∈ M) ∧ (∀ l, algebraMap A P (a l) = algebraMap A P (s l) * x l) ∧
      ∃ b' : Module.Basis ι k (k ⊗[A] Ω[A⁄k]), ∀ l, b' l = (1 : k) ⊗ₜ[A] D k A (a l) := by
  classical
  choose as has using fun l ↦ IsLocalization.surj M (x l)
  let a : ι → A := fun l ↦ (as l).1
  let s : ι → A := fun l ↦ ((as l).2 : A)
  have hsM : ∀ l, s l ∈ M := fun l ↦ (as l).2.2
  have has' : ∀ l, algebraMap A P (a l) = algebraMap A P (s l) * x l := fun l ↦ by
    change algebraMap A P (as l).1 = algebraMap A P ((as l).2 : A) * x l
    rw [← has l, mul_comm]
  haveI : Algebra.FormallyEtale A P := Algebra.FormallyEtale.of_isLocalization (Rₘ := P) M
  let θ : k ⊗[A] Ω[A⁄k] ≃ₗ[k] k ⊗[P] Ω[P⁄k] := cotangentEquivOfFormallyEtale

  let c : ι → k := fun l ↦ algebraMap A k (s l)
  have hc : ∀ l, IsUnit (c l) := fun l ↦ isUnit_iff_ne_zero.mpr (hM _ (hsM l))
  have hθ : ∀ l, θ ((1 : k) ⊗ₜ[A] D k A (a l)) = c l • b l := by
    intro l
    change cotangentEquivOfFormallyEtale ((1 : k) ⊗ₜ[A] D k A (a l)) = c l • b l
    rw [cotangentEquivOfFormallyEtale_one_tmul_D, has', Derivation.leibniz, TensorProduct.tmul_add,
      one_tmul_smul, one_tmul_smul, hx, zero_smul, add_zero, hb, ← IsScalarTower.algebraMap_apply A P k]
  refine ⟨a, s, hsM, has', (b.isUnitSMul hc).map θ.symm, fun l ↦ ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.isUnitSMul_apply, ← hθ, LinearEquiv.symm_apply_apply]

theorem ker_le_map_includeLeft_sup_map_includeRight
    {k : Type u} [Field k] {B C : Type u} [CommRing B] [CommRing C] [Algebra k B] [Algebra k C]
    (ψ : B ⊗[k] C →ₐ[k] k) :
    RingHom.ker ψ.toRingHom ≤
      (RingHom.ker (ψ.comp Algebra.TensorProduct.includeLeft).toRingHom).map
          (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] C).toRingHom ⊔
        (RingHom.ker (ψ.comp Algebra.TensorProduct.includeRight).toRingHom).map
          (Algebra.TensorProduct.includeRight : C →ₐ[k] B ⊗[k] C).toRingHom := by
  classical
  set εB : B →ₐ[k] k := ψ.comp Algebra.TensorProduct.includeLeft with hεB
  set εC : C →ₐ[k] k := ψ.comp Algebra.TensorProduct.includeRight with hεC
  set JB : Ideal (B ⊗[k] C) := (RingHom.ker εB.toRingHom).map
    (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] C).toRingHom with hJB
  set JC : Ideal (B ⊗[k] C) := (RingHom.ker εC.toRingHom).map
    (Algebra.TensorProduct.includeRight : C →ₐ[k] B ⊗[k] C).toRingHom with hJC

  let γ : B ⊗[k] C →ₗ[k] C := (TensorProduct.lid k C).toLinearMap ∘ₗ TensorProduct.map εB.toLinearMap LinearMap.id
  have hγ : ∀ (b : B) (c : C), γ (b ⊗ₜ c) = εB b • c := fun b c ↦ by
    simp [γ]

  have hcong : ∀ x : B ⊗[k] C, x - (1 : B) ⊗ₜ γ x ∈ JB := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      rw [hγ, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, ← TensorProduct.sub_tmul]
      have : (b - algebraMap k B (εB b)) ⊗ₜ[k] c =
          Algebra.TensorProduct.includeLeft (S := k) (b - algebraMap k B (εB b)) * ((1 : B) ⊗ₜ[k] c) := by
        rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
      rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sub, AlgHom.commutes,
        Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    | add x y hx hy =>
      have : x + y - (1 : B) ⊗ₜ[k] γ (x + y) = (x - (1 : B) ⊗ₜ γ x) + (y - (1 : B) ⊗ₜ γ y) := by
        rw [map_add, TensorProduct.tmul_add]; abel
      rw [this]; exact Ideal.add_mem _ hx hy

  have hJBψ : JB ≤ RingHom.ker ψ.toRingHom := by
    rw [hJB, Ideal.map_le_iff_le_comap]
    intro b hb
    simpa [RingHom.mem_ker, hεB] using hb
  intro x hx
  have h1 : (1 : B) ⊗ₜ[k] γ x ∈ RingHom.ker ψ.toRingHom := by
    have := Ideal.sub_mem _ hx (hJBψ (hcong x))
    rwa [sub_sub_cancel] at this
  have h2 : (1 : B) ⊗ₜ[k] γ x ∈ JC := by
    rw [hJC]
    refine Ideal.mem_map_of_mem (Algebra.TensorProduct.includeRight : C →ₐ[k] B ⊗[k] C).toRingHom ?_
    rw [RingHom.mem_ker]
    simpa [RingHom.mem_ker, hεC, Algebra.TensorProduct.includeRight_apply] using h1
  have : x = (x - (1 : B) ⊗ₜ γ x) + (1 : B) ⊗ₜ γ x := by abel
  rw [this]
  exact Submodule.add_mem_sup (hcong x) h2

lemma etale_comp_of_bijective {R₁ R₂ S : Type*} [CommRing R₁] [CommRing R₂] [CommRing S]
    (g : R₁ →+* R₂) (hg : Function.Bijective g) (f : R₂ →+* S) (hf : f.Etale) : (f.comp g).Etale := by
  letI := g.toAlgebra
  letI := f.toAlgebra
  letI := (f.comp g).toAlgebra
  haveI : IsScalarTower R₁ R₂ S := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : Algebra.Etale R₁ R₂ := RingHom.etale_algebraMap.mp (RingHom.Etale.of_bijective hg)
  haveI : Algebra.Etale R₂ S := RingHom.etale_algebraMap.mp hf
  exact RingHom.etale_algebraMap.mpr (Algebra.Etale.comp R₁ R₂ S)

lemma etale_comp_iff_of_bijective {R₁ R₂ S : Type*} [CommRing R₁] [CommRing R₂] [CommRing S]
    (g : R₁ →+* R₂) (hg : Function.Bijective g) (f : R₂ →+* S) : (f.comp g).Etale ↔ f.Etale := by
  refine ⟨fun h ↦ ?_, etale_comp_of_bijective g hg f⟩
  let e : R₁ ≃+* R₂ := RingEquiv.ofBijective g hg
  have hfe : f = (f.comp g).comp e.symm.toRingHom := by
    ext x
    change f x = f (g (e.symm x))
    exact congrArg f (e.apply_symm_apply x).symm
  rw [hfe]
  exact etale_comp_of_bijective _ e.symm.bijective _ h

universe v w in
theorem etale_aeval_iff_of_equiv {k : Type u} [Field k] {A' : Type u} [CommRing A'] [Algebra k A']
    {ι : Type v} {ι' : Type w} (e : ι ≃ ι') (a : ι' → A') :
    (MvPolynomial.aeval (a ∘ e) : MvPolynomial ι k →ₐ[k] A').toRingHom.Etale ↔
      (MvPolynomial.aeval a : MvPolynomial ι' k →ₐ[k] A').toRingHom.Etale := by
  have hcomp : (MvPolynomial.aeval (a ∘ e) : MvPolynomial ι k →ₐ[k] A').toRingHom =
      (MvPolynomial.aeval a : MvPolynomial ι' k →ₐ[k] A').toRingHom.comp
        (MvPolynomial.rename e : MvPolynomial ι k →ₐ[k] MvPolynomial ι' k).toRingHom := by
    have : (MvPolynomial.aeval (a ∘ e) : MvPolynomial ι k →ₐ[k] A') =
        (MvPolynomial.aeval a).comp (MvPolynomial.rename e) := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [AlgHom.comp_apply, MvPolynomial.aeval_rename]
    rw [this]; rfl
  rw [hcomp]
  exact etale_comp_iff_of_bijective _ (MvPolynomial.renameEquiv k e).bijective _

theorem mvPolynomial_isStandardSmoothOfRelativeDimension (k : Type u) [CommRing k] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n k (MvPolynomial (Fin n) k) := by
  classical
  let v : PEmpty.{1} → MvPolynomial (Fin n) k := PEmpty.elim
  let P₀ := Algebra.PreSubmersivePresentation.naive (R := k) (v := v) PEmpty.elim (fun a => a.elim)
  let P₁ : Algebra.SubmersivePresentation k (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range v)) (Fin n) PEmpty.{1} :=
    { toPreSubmersivePresentation := P₀
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_isEmpty, map_one]
        exact isUnit_one }
  have hbot : Ideal.span (Set.range v) = ⊥ := by simp [v, Set.range_eq_empty]
  let e : (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range v)) ≃ₐ[k] MvPolynomial (Fin n) k :=
    (Ideal.quotientEquivAlgOfEq k hbot).trans (AlgEquiv.quotientBot k (MvPolynomial (Fin n) k))
  exact (P₁.ofAlgEquiv e).isStandardSmoothOfRelativeDimension (by
    simp [Algebra.Presentation.dimension])

open AlgebraicGeometry in
theorem smoothOfRelativeDimension_SpecMap_of_isStandardSmoothOfRelativeDimension
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ)
    (h : φ.IsStandardSmoothOfRelativeDimension n) :
    SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom φ)) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ h

open AlgebraicGeometry in
theorem smoothOfRelativeDimension_SpecMap_mvPolynomial (k : Type u) [CommRing k] (n : ℕ) :
    SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k)))) := by
  apply smoothOfRelativeDimension_SpecMap_of_isStandardSmoothOfRelativeDimension
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact mvPolynomial_isStandardSmoothOfRelativeDimension k n

noncomputable def quotSpanXInlEquiv (k : Type u) [Field k] (h m : ℕ) :
    (MvPolynomial (Fin h ⊕ Fin m) k ⧸
      Ideal.span (Set.range ((MvPolynomial.X : Fin h ⊕ Fin m → MvPolynomial (Fin h ⊕ Fin m) k) ∘ Sum.inl))) ≃ₐ[k]
      MvPolynomial (Fin m) k := by
  let I : Ideal (MvPolynomial (Fin h ⊕ Fin m) k) :=
    Ideal.span (Set.range ((MvPolynomial.X : Fin h ⊕ Fin m → MvPolynomial (Fin h ⊕ Fin m) k) ∘ Sum.inl))
  let pr : MvPolynomial (Fin h ⊕ Fin m) k →ₐ[k] MvPolynomial (Fin m) k :=
    MvPolynomial.aeval (Sum.elim (fun _ ↦ 0) MvPolynomial.X)
  have hpr : ∀ x ∈ I, pr x = 0 := by
    intro x hx
    have : I ≤ RingHom.ker pr.toRingHom := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp [pr]
    exact this hx
  let f : (MvPolynomial (Fin h ⊕ Fin m) k ⧸ I) →ₐ[k] MvPolynomial (Fin m) k := Ideal.Quotient.liftₐ I pr hpr
  let g : MvPolynomial (Fin m) k →ₐ[k] (MvPolynomial (Fin h ⊕ Fin m) k ⧸ I) :=
    (Ideal.Quotient.mkₐ k I).comp (MvPolynomial.rename Sum.inr)
  have hf : ∀ p, f (Ideal.Quotient.mkₐ k I p) = pr p := fun p ↦ rfl
  have hprX : ∀ s, pr (MvPolynomial.X s) = Sum.elim (fun _ ↦ (0 : MvPolynomial (Fin m) k)) MvPolynomial.X s :=
    fun s ↦ MvPolynomial.aeval_X _ s
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply MvPolynomial.algHom_ext
    intro j
    change f (Ideal.Quotient.mkₐ k I (MvPolynomial.rename Sum.inr (MvPolynomial.X j))) = MvPolynomial.X j
    rw [hf, MvPolynomial.rename_X, hprX, Sum.elim_inr]
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    rintro (i | j)
    · have h0 : (Ideal.Quotient.mkₐ k I) (MvPolynomial.X (Sum.inl i)) = 0 := by
        rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span ⟨i, rfl⟩
      change Ideal.Quotient.mkₐ k I (MvPolynomial.rename Sum.inr (f (Ideal.Quotient.mkₐ k I (MvPolynomial.X (Sum.inl i)))))
        = Ideal.Quotient.mkₐ k I (MvPolynomial.X (Sum.inl i))
      rw [hf, hprX, Sum.elim_inl, map_zero, map_zero, h0]
    · change Ideal.Quotient.mkₐ k I (MvPolynomial.rename Sum.inr (f (Ideal.Quotient.mkₐ k I (MvPolynomial.X (Sum.inr j)))))
        = Ideal.Quotient.mkₐ k I (MvPolynomial.X (Sum.inr j))
      rw [hf, hprX, Sum.elim_inr, MvPolynomial.rename_X]

open AlgebraicGeometry in
theorem smoothOfRelativeDimension_SpecMap_quotient_of_etale_aeval
    {k : Type u} [Field k] {A' : Type u} [CommRing A'] [Algebra k A'] {h m : ℕ}
    (a : Fin h ⊕ Fin m → A')
    (ha : (MvPolynomial.aeval a : MvPolynomial (Fin h ⊕ Fin m) k →ₐ[k] A').toRingHom.Etale) :
    SmoothOfRelativeDimension m
      (Spec.map (CommRingCat.ofHom (algebraMap k (A' ⧸ Ideal.span (Set.range (a ∘ Sum.inl)))))) := by
  classical
  let R := MvPolynomial (Fin h ⊕ Fin m) k
  letI algRA : Algebra R A' := (MvPolynomial.aeval a : R →ₐ[k] A').toRingHom.toAlgebra
  haveI : IsScalarTower k R A' := IsScalarTower.of_algebraMap_eq fun c ↦
    ((MvPolynomial.aeval a : R →ₐ[k] A').commutes c).symm
  haveI : Algebra.Etale R A' := ha.toAlgebra
  let I : Ideal R := Ideal.span (Set.range ((MvPolynomial.X : Fin h ⊕ Fin m → R) ∘ Sum.inl))
  have hX : ∀ s, algebraMap R A' (MvPolynomial.X s) = a s := fun s ↦ MvPolynomial.aeval_X a s
  have hJ : I.map (algebraMap R A') = Ideal.span (Set.range (a ∘ Sum.inl)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 1
    ext i
    simp only [Set.mem_range, Function.comp_apply, hX]
  rw [← hJ]
  haveI : IsScalarTower k (R ⧸ I) (A' ⧸ I.map (algebraMap R A')) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      calc algebraMap k (A' ⧸ I.map (algebraMap R A')) c
          = Ideal.Quotient.mk (I.map (algebraMap R A')) (algebraMap k A' c) := rfl
        _ = Ideal.Quotient.mk (I.map (algebraMap R A')) (algebraMap R A' (algebraMap k R c)) := by
            rw [← IsScalarTower.algebraMap_apply k R A']
        _ = algebraMap (R ⧸ I) (A' ⧸ I.map (algebraMap R A')) (Ideal.Quotient.mk I (algebraMap k R c)) :=
            (Ideal.Quotient.algebraMap_quotient_map_quotient _).symm
        _ = algebraMap (R ⧸ I) (A' ⧸ I.map (algebraMap R A')) (algebraMap k (R ⧸ I) c) := rfl

  haveI : Algebra.Etale (R ⧸ I) (A' ⧸ I.map (algebraMap R A')) :=
    Algebra.Etale.of_equiv (R := R ⧸ I) (A := (R ⧸ I) ⊗[R] A') (B := A' ⧸ I.map (algebraMap R A'))
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A' I).symm
  have hψ : (algebraMap (R ⧸ I) (A' ⧸ I.map (algebraMap R A'))).Etale := RingHom.etale_algebraMap.mpr ‹_›

  let e : (R ⧸ I) ≃ₐ[k] MvPolynomial (Fin m) k := quotSpanXInlEquiv k h m
  have hθ : ((algebraMap (R ⧸ I) (A' ⧸ I.map (algebraMap R A'))).comp e.symm.toRingEquiv.toRingHom).Etale :=
    etale_comp_of_bijective _ e.symm.bijective _ hψ

  have hfac : algebraMap k (A' ⧸ I.map (algebraMap R A')) =
      ((algebraMap (R ⧸ I) (A' ⧸ I.map (algebraMap R A'))).comp e.symm.toRingEquiv.toRingHom).comp
        (algebraMap k (MvPolynomial (Fin m) k)) := by
    ext c
    simp only [RingHom.comp_apply]
    change algebraMap k _ c = algebraMap (R ⧸ I) _ (e.symm (algebraMap k (MvPolynomial (Fin m) k) c))
    rw [e.symm.commutes, ← IsScalarTower.algebraMap_apply]
  rw [hfac, CommRingCat.ofHom_comp, Spec.map_comp]
  haveI h0 : SmoothOfRelativeDimension 0 (Spec.map (CommRingCat.ofHom
      ((algebraMap (R ⧸ I) (A' ⧸ I.map (algebraMap R A'))).comp e.symm.toRingEquiv.toRingHom))) := by
    have : AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom
        ((algebraMap (R ⧸ I) (A' ⧸ I.map (algebraMap R A'))).comp e.symm.toRingEquiv.toRingHom))) := by
      rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
      exact hθ
    infer_instance
  haveI hm : SmoothOfRelativeDimension m (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin m) k)))) :=
    smoothOfRelativeDimension_SpecMap_mvPolynomial k m
  have := smoothOfRelativeDimension_comp 0 m
    (Spec.map (CommRingCat.ofHom
      ((algebraMap (R ⧸ I) (A' ⧸ I.map (algebraMap R A'))).comp e.symm.toRingEquiv.toRingHom)))
    (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin m) k))))
  rwa [Nat.zero_add] at this

theorem formallyUnramified_of_span_eq_maximalIdeal
    {k : Type u} [Field k] {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] (hφ : φ.EssFiniteType) (ι₀ : k →+* R)
    (hk : Function.Surjective ((IsLocalRing.residue S).comp (φ.comp ι₀)))
    {ι : Type} [Finite ι] (x : ι → R) (y : ι → S) (hx : ∀ l, x l ∈ IsLocalRing.maximalIdeal R)
    (hy : IsLocalRing.maximalIdeal S = Ideal.span (Set.range y))
    (hxy : ∀ l, φ (x l) - y l ∈ IsLocalRing.maximalIdeal S ^ 2) :
    φ.FormallyUnramified := by
  classical
  letI := φ.toAlgebra
  haveI hloc : IsLocalHom (algebraMap R S) := ‹IsLocalHom φ›
  haveI : Algebra.EssFiniteType R S := hφ
  open IsLocalRing in

  have hle : (maximalIdeal R).map (algebraMap R S) ≤ maximalIdeal S := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu ↦ (mem_maximalIdeal _ |>.mp ha) (IsLocalHom.map_nonunit a hu)
  have hmap : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S := by
    apply le_antisymm hle
    have hfg : (maximalIdeal S).FG := by
      rw [hy]; exact ⟨(Set.finite_range y).toFinset, by simp⟩
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal S) hfg ?_ ?_
    · rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · have : Ideal.span (Set.range y) ≤
          (maximalIdeal R).map (algebraMap R S) ⊔ maximalIdeal S • maximalIdeal S := by
        rw [Ideal.span_le]
        rintro _ ⟨l, rfl⟩
        have ha : φ (x l) ∈ (maximalIdeal R).map (algebraMap R S) ⊔ maximalIdeal S • maximalIdeal S :=
          Submodule.mem_sup_left (Ideal.mem_map_of_mem _ (hx l))
        have hb : φ (x l) - y l ∈ (maximalIdeal R).map (algebraMap R S) ⊔ maximalIdeal S • maximalIdeal S := by
          refine Submodule.mem_sup_right ?_
          rw [Ideal.smul_eq_mul, ← pow_two]
          exact hxy l
        have := Submodule.sub_mem _ ha hb
        rwa [sub_sub_cancel] at this
      exact hy.le.trans this

  have hsurj : Function.Surjective (algebraMap (ResidueField R) (ResidueField S)) := by
    intro z
    obtain ⟨c, rfl⟩ := hk z
    refine ⟨residue R (ι₀ c), ?_⟩
    change algebraMap (ResidueField R) (ResidueField S) (algebraMap R (ResidueField R) (ι₀ c)) =
      algebraMap S (ResidueField S) (algebraMap R S (ι₀ c))
    rw [← IsScalarTower.algebraMap_apply R (ResidueField R) (ResidueField S),
      IsScalarTower.algebraMap_apply R S (ResidueField S)]
  haveI : Algebra.IsSeparable (ResidueField R) (ResidueField S) := by
    let e := AlgEquiv.ofBijective (Algebra.ofId (ResidueField R) (ResidueField S))
      ⟨(algebraMap (ResidueField R) (ResidueField S)).injective, hsurj⟩
    exact Algebra.IsSeparable.of_algHom (ResidueField R) (ResidueField R) e.symm.toAlgHom
  exact Algebra.FormallyUnramified.of_map_maximalIdeal hmap

end CutAlg

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace IsLocalRing

namespace CutGeo

variable {k : Type u} [Field k]

@[reducible] noncomputable def secAlgebra {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k)) (U : Y.Opens) :
    Algebra k Γ(Y, U) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appLE ⊤ U le_top).hom.toAlgebra

@[reducible] noncomputable def stalkAlgebra {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k)) (y : Y) :
    Algebra k (Y.presheaf.stalk y) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom.toAlgebra

section towers

variable {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k))

theorem isScalarTower_sec_stalk (U : Y.Opens) (y : Y) (hy : y ∈ U) :
    letI := secAlgebra p U; letI := stalkAlgebra p y
    letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hy⟩ : U)
    IsScalarTower k Γ(Y, U) (Y.presheaf.stalk y) := by
  letI := secAlgebra p U; letI := stalkAlgebra p y
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hy⟩ : U)
  refine IsScalarTower.of_algebraMap_eq' ?_
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom =
    (Y.presheaf.germ U y hy).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appLE ⊤ U le_top).hom
  rw [← CommRingCat.hom_comp]
  simp only [Category.assoc, Scheme.Hom.appLE, TopCat.Presheaf.germ_res]
  rfl

theorem stalkMap_comp_algebraMap {X : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    letI := stalkAlgebra p (f.base x); letI := stalkAlgebra (f ≫ p) x
    (f.stalkMap x).hom.comp (algebraMap k (Y.presheaf.stalk (f.base x))) =
      algebraMap k (X.presheaf.stalk x) := by
  letI := stalkAlgebra p (f.base x); letI := stalkAlgebra (f ≫ p) x
  change (f.stalkMap x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ (f.base x) trivial).hom =
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ p).appTop ≫ X.presheaf.germ ⊤ x trivial).hom
  rw [← CommRingCat.hom_comp]
  simp only [Category.assoc, Scheme.Hom.germ_stalkMap, Scheme.Hom.comp_appTop]
  rfl

theorem fromSpec_comp {V : Y.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ p = Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appLE ⊤ V le_top) := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hV (U := ⊤) (fun _ _ => trivial)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
  rw [Spec.map_comp, this]

end towers

section ratpoint

variable {Y : Scheme.{u}}

theorem stalkClosedPointTo_comp_algebraMap (p : Y ⟶ Spec (.of k)) (y : Spec (.of k) ⟶ Y) (hy : y ≫ p = 𝟙 _) :
    letI := stalkAlgebra p (y.base (closedPoint k))
    (Scheme.stalkClosedPointTo y).hom.comp (algebraMap k (Y.presheaf.stalk (y.base (closedPoint k)))) =
      RingHom.id k := by
  letI := stalkAlgebra p (y.base (closedPoint k))
  suffices H : (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ _ trivial ≫ Scheme.stalkClosedPointTo y =
      𝟙 _ by
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ _ trivial) ≫ Scheme.stalkClosedPointTo y).hom = _
    simp only [Category.assoc] at H ⊢
    rw [H]; rfl
  rw [Scheme.germ_stalkClosedPointTo y ⊤ trivial, ← Category.assoc (p.appTop),
    show p.appTop ≫ y.app ⊤ = (y ≫ p).app ⊤ from (Scheme.Hom.comp_app _ _ _).symm, Scheme.Hom.congr_app hy ⊤]
  simp only [Scheme.Hom.id_app, Category.id_comp, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    Category.assoc, ← Functor.map_comp_assoc, ← op_comp, eqToHom_trans, eqToHom_op, eqToHom_map]
  simp

theorem residue_comp_algebraMap_surjective (p : Y ⟶ Spec (.of k)) (y : Spec (.of k) ⟶ Y) (hy : y ≫ p = 𝟙 _) :
    letI := stalkAlgebra p (y.base (closedPoint k))
    Function.Surjective
      ((residue (Y.presheaf.stalk (y.base (closedPoint k)))).comp
        (algebraMap k (Y.presheaf.stalk (y.base (closedPoint k))))) := by
  letI := stalkAlgebra p (y.base (closedPoint k))
  have hret := stalkClosedPointTo_comp_algebraMap p y hy
  intro c
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨(Scheme.stalkClosedPointTo y).hom s, ?_⟩
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [Ideal.Quotient.eq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := hu.map (Scheme.stalkClosedPointTo y).hom
  rw [map_sub, ← RingHom.comp_apply, hret, RingHom.id_apply, sub_self] at this
  exact not_isUnit_zero this

theorem ker_stalkClosedPointTo (y : Spec (.of k) ⟶ Y) :
    RingHom.ker (Scheme.stalkClosedPointTo y).hom = maximalIdeal (Y.presheaf.stalk (y.base (closedPoint k))) := by
  ext s
  rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    ← isUnit_map_iff (Scheme.stalkClosedPointTo y).hom, isUnit_iff_ne_zero, not_not]

theorem SpecMap_germ_stalkClosedPointTo_fromSpec (y : Spec (.of k) ⟶ Y) {V : Y.Opens} (hV : IsAffineOpen V)
    (hyV : y.base (closedPoint k) ∈ V) :
    Spec.map (Y.presheaf.germ V _ hyV ≫ Scheme.stalkClosedPointTo y) ≫ hV.fromSpec = y := by
  rw [Spec.map_comp, Category.assoc]
  change Spec.map (Scheme.stalkClosedPointTo y) ≫ hV.fromSpecStalk hyV = y
  rw [hV.fromSpecStalk_eq_fromSpecStalk hyV]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk y

theorem primeIdealOf_eq_ker (y : Spec (.of k) ⟶ Y) {V : Y.Opens} (hV : IsAffineOpen V) (hyV : y.base (closedPoint k) ∈ V) :
    (hV.primeIdealOf ⟨_, hyV⟩).asIdeal =
      RingHom.ker (Y.presheaf.germ V _ hyV ≫ Scheme.stalkClosedPointTo y).hom := by
  rw [IsAffineOpen.primeIdealOf_eq_map_closedPoint, CommRingCat.hom_comp, ← RingHom.comap_ker,
    ker_stalkClosedPointTo]
  rfl

end ratpoint

section smooth

variable {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n p]

theorem exists_isStandardSmoothOfRelativeDimension_chart (y : Y) :
    ∃ (V : Y.Opens) (hV : IsAffineOpen V) (hyV : y ∈ V),
      letI := secAlgebra p V; Algebra.IsStandardSmoothOfRelativeDimension n k Γ(Y, V) := by
  obtain ⟨U, hU, V, hV, hyV, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := p) y
  refine ⟨V, hV, hyV, ?_⟩
  have hpt : ∀ x : ↑(Spec (CommRingCat.of k)), x = closedPoint k := fun x =>
    PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm)
  have hU' : U = ⊤ := IsLocalRing.closed_point_mem_iff.mp (hpt (p.base y) ▸ e hyV)
  subst hU'
  exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).2 (p.appLE ⊤ V e).hom
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv hstd

theorem nonempty_basis_kaehler_stalk (y : Y) :
    letI := stalkAlgebra p y
    Nonempty (Module.Basis (Fin n) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄k])) :=
  AlgebraicGeometry.SmoothOfRelativeDimension.nonempty_basis_kaehlerDifferential_stalk p n y

end smooth

theorem maximalIdeal_stalk_pullback_le {Y Z : Scheme.{u}} (pY : Y ⟶ Spec (.of k)) (pZ : Z ⟶ Spec (.of k))
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ pY = 𝟙 _) (zz : Spec (.of k) ⟶ Z) (hz : zz ≫ pZ = 𝟙 _)
    (w : ↑(pullback pY pZ)) (hw : w = (pullback.lift y zz (hy.trans hz.symm)).base (closedPoint k)) :
    maximalIdeal ((pullback pY pZ).presheaf.stalk w) ≤
      (maximalIdeal _).map ((pullback.fst pY pZ).stalkMap w).hom ⊔
        (maximalIdeal _).map ((pullback.snd pY pZ).stalkMap w).hom :=
  AlgebraicGeometry.maximalIdeal_stalk_pullback_le_of_sections pY pZ y hy zz hz w hw

theorem germ_mem_maximalIdeal_iff_of_eq {X : Scheme.{u}} {U : X.Opens} {x x' : ↑X} (h : x = x')
    (hx : x ∈ U) (hx' : x' ∈ U) (s : Γ(X, U)) :
    (X.presheaf.germ U x hx).hom s ∈ maximalIdeal (X.presheaf.stalk x) ↔
      (X.presheaf.germ U x' hx').hom s ∈ maximalIdeal (X.presheaf.stalk x') := by
  subst h; rfl

theorem germ_eq_zero_iff_of_eq {X : Scheme.{u}} {U : X.Opens} {x x' : ↑X} (h : x = x')
    (hx : x ∈ U) (hx' : x' ∈ U) (s : Γ(X, U)) :
    (X.presheaf.germ U x hx).hom s = 0 ↔ (X.presheaf.germ U x' hx').hom s = 0 := by
  subst h; rfl

theorem map_maximalIdeal_stalkMap_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hf : Function.Surjective (f.stalkMap x).hom) :
    (maximalIdeal (Y.presheaf.stalk (f.base x))).map (f.stalkMap x).hom = maximalIdeal (X.presheaf.stalk x) :=
  IsLocalRing.map_maximalIdeal_of_surjective _ hf

end CutGeo

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw.germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq actionSource actionFstPoint actionSndPoint action action_def actionFstPoint_coe actionSndPoint_coe action_over pointGroup mul_one one mul_natural mk inv one_mul mul"
namespace CutBody
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_affine_formallyUnramified_stalkMap_action_one.GoodReductionJacobian IsLocalRing TopologicalSpace"
open scoped TensorProduct

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}

theorem comp_one_eq_one (L : RelativeGroupLaw k f) {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f))
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    NeronModelInfra.schemeHomOverComp (LN.one t) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = L.one t := by
  letI := L.pointGroup t
  have h1 := hi t (LN.one t) (LN.one t)
  rw [LN.one_mul] at h1
  have h2 : NeronModelInfra.schemeHomOverComp (LN.one t) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) *
      NeronModelInfra.schemeHomOverComp (LN.one t) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
      NeronModelInfra.schemeHomOverComp (LN.one t) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) := h1.symm
  exact mul_eq_left.mp h2

noncomputable abbrev mult (L : RelativeGroupLaw k f) : pullback f f ⟶ G :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1

theorem lift_one_one_comp_mult (L : RelativeGroupLaw k f) :
    pullback.lift (L.one (𝟙 _)).1 (L.one (𝟙 _)).1 rfl ≫ mult L = (L.one (𝟙 _)).1 := by
  set ψ : Spec (CommRingCat.of k) ⟶ pullback f f :=
    pullback.lift (L.one (𝟙 (Spec (CommRingCat.of k)))).1 (L.one (𝟙 (Spec (CommRingCat.of k)))).1 rfl with hψdef
  have hψ : ψ ≫ (pullback.fst f f ≫ f) = 𝟙 _ := by
    rw [← Category.assoc, hψdef, pullback.lift_fst]; exact (L.one _).2
  have hnat := congrArg Subtype.val (L.mul_natural (pullback.fst f f ≫ f) (𝟙 _) ψ hψ ⟨pullback.fst f f, rfl⟩
    ⟨pullback.snd f f, pullback.condition.symm⟩)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at hnat
  change ψ ≫ _ = _
  rw [hnat]
  have h1 : GoodReductionJacobian.schemeHomOverComp ψ hψ
      (⟨pullback.fst f f, rfl⟩ : SchemeHomOver (pullback.fst f f ≫ f) f) = L.one (𝟙 _) :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, hψdef, pullback.lift_fst])
  have h2 : GoodReductionJacobian.schemeHomOverComp ψ hψ
      (⟨pullback.snd f f, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst f f ≫ f) f) = L.one (𝟙 _) :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, hψdef, pullback.lift_snd])
  rw [h1, h2, L.one_mul]

theorem map_comp_action_eq_map_comp_mul (L : RelativeGroupLaw k f)
    {N S : Scheme.{u}} (i : N ⟶ G) (j : S ⟶ G) :
    pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
        ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i =
      pullback.map (i ≫ f) (j ≫ f) f f i j (𝟙 _) (Category.comp_id _) (Category.comp_id _) ≫ mult L := by
  set ψ₁ : pullback (i ≫ f) f ⟶ pullback f f :=
    pullback.map (i ≫ f) f f f i (𝟙 G) (𝟙 _) (Category.comp_id _) (by simp) with hψ₁def
  have hψ₁ : ψ₁ ≫ (pullback.fst f f ≫ f) = actionSource f i := by
    rw [← Category.assoc]
    erw [pullback.lift_fst]
    rw [Category.assoc, pullback.condition]
  have key : ψ₁ ≫ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩
      ⟨pullback.snd f f, pullback.condition.symm⟩).1 = L.action i := by
    have hnat := congrArg Subtype.val (L.mul_natural (pullback.fst f f ≫ f) (actionSource f i) ψ₁ hψ₁
      ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at hnat
    rw [hnat, action_def]
    have h1 : GoodReductionJacobian.schemeHomOverComp ψ₁ hψ₁ (⟨pullback.fst f f, rfl⟩ : SchemeHomOver (pullback.fst f f ≫ f) f) =
        L.actionFstPoint i := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, actionFstPoint_coe, ψ₁]
      erw [pullback.lift_fst]
    have h2 : GoodReductionJacobian.schemeHomOverComp ψ₁ hψ₁
        (⟨pullback.snd f f, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst f f ≫ f) f) = L.actionSndPoint i := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, actionSndPoint_coe, ψ₁]
      erw [pullback.lift_snd]
      simp
    rw [h1, h2]
  rw [← key, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc]
    simp
  · simp only [Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]

theorem germ_mult_sub_mem_sq (L : RelativeGroupLaw k f) (U : G.Opens)
    (he : (L.one (𝟙 (Spec (CommRingCat.of k)))).1.base (closedPoint k) ∈ U)
    (p : ↑(pullback f f))
    (hp : p = (pullback.lift (L.one (𝟙 (Spec (CommRingCat.of k)))).1 (L.one (𝟙 (Spec (CommRingCat.of k)))).1 rfl).base
      (closedPoint k))
    (hpm : p ∈ mult L ⁻¹ᵁ U) (hp₁ : p ∈ pullback.fst f f ⁻¹ᵁ U) (hp₂ : p ∈ pullback.snd f f ⁻¹ᵁ U)
    (φ : Γ(G, U)) (hφ : (G.presheaf.germ U _ he).hom φ ∈ maximalIdeal (G.presheaf.stalk _)) :
    ((pullback f f).presheaf.germ (mult L ⁻¹ᵁ U ⊓ pullback.fst f f ⁻¹ᵁ U ⊓ pullback.snd f f ⁻¹ᵁ U) p
        (Opens.mem_inf.mpr ⟨Opens.mem_inf.mpr ⟨hpm, hp₁⟩, hp₂⟩)).hom
      (((mult L).appLE U _ (inf_le_left.trans inf_le_left)).hom φ -
        ((pullback.fst f f).appLE U _ (inf_le_left.trans inf_le_right)).hom φ -
        ((pullback.snd f f).appLE U _ inf_le_right).hom φ)
      ∈ maximalIdeal ((pullback f f).presheaf.stalk p) ^ 2 := by
  subst hp
  exact GoodReductionJacobian.RelativeGroupLaw.germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq f L U _
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right he _ φ hφ

theorem germ_sub_sub_mem_sq (L : RelativeGroupLaw k f) (U : G.Opens)
    (he : (L.one (𝟙 (Spec (CommRingCat.of k)))).1.base (closedPoint k) ∈ U)
    {X : Scheme.{u}} (ρ : X ⟶ pullback f f) (z : X)
    (hz : ρ.base z = (pullback.lift (L.one (𝟙 (Spec (CommRingCat.of k)))).1
      (L.one (𝟙 (Spec (CommRingCat.of k)))).1 rfl).base (closedPoint k))
    (a b c : X ⟶ G) (ha : ρ ≫ mult L = a) (hb : ρ ≫ pullback.fst f f = b) (hc : ρ ≫ pullback.snd f f = c)
    (haz : a.base z ∈ U) (hbz : b.base z ∈ U) (hcz : c.base z ∈ U)
    (φ : Γ(G, U)) (hφ : (G.presheaf.germ U _ he).hom φ ∈ maximalIdeal (G.presheaf.stalk _)) :
    (X.presheaf.germ (a ⁻¹ᵁ U) z haz).hom (a.app U φ) - (X.presheaf.germ (b ⁻¹ᵁ U) z hbz).hom (b.app U φ)
      - (X.presheaf.germ (c ⁻¹ᵁ U) z hcz).hom (c.app U φ) ∈ maximalIdeal (X.presheaf.stalk z) ^ 2 := by
  subst ha hb hc
  set W : (pullback f f).Opens := mult L ⁻¹ᵁ U ⊓ pullback.fst f f ⁻¹ᵁ U ⊓ pullback.snd f f ⁻¹ᵁ U with hW
  have hzW : z ∈ ρ ⁻¹ᵁ W := Opens.mem_inf.mpr ⟨Opens.mem_inf.mpr ⟨haz, hbz⟩, hcz⟩

  have H : ∀ (m : pullback f f ⟶ G) (e : W ≤ m ⁻¹ᵁ U) (hmz : (ρ ≫ m).base z ∈ U),
      (X.presheaf.germ (ρ ⁻¹ᵁ W) z hzW).hom ((ρ.app W).hom ((m.appLE U W e).hom φ)) =
        (X.presheaf.germ ((ρ ≫ m) ⁻¹ᵁ U) z hmz).hom (((ρ ≫ m).app U).hom φ) := by
    intro m e hmz
    have : m.appLE U W e ≫ ρ.app W ≫ X.presheaf.germ (ρ ⁻¹ᵁ W) z hzW =
        (ρ ≫ m).app U ≫ X.presheaf.germ ((ρ ≫ m) ⁻¹ᵁ U) z hmz := by
      rw [Scheme.Hom.app_eq_appLE ρ, ← Category.assoc, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE,
        Category.assoc, TopCat.Presheaf.germ_res]
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using congrArg (fun ψ => ψ.hom φ) this
  have hp := germ_mult_sub_mem_sq L U he (ρ.base z) hz haz hbz hcz φ hφ
  have hmap := Ideal.mem_map_of_mem (ρ.stalkMap z).hom hp
  rw [Ideal.map_pow] at hmap
  have hle : (maximalIdeal _).map (ρ.stalkMap z).hom ≤ maximalIdeal (X.presheaf.stalk z) :=
map_maximalIdeal_le _
  have hmem := Ideal.pow_right_mono hle 2 hmap
  rw [Scheme.Hom.germ_stalkMap_apply ρ W z hzW, map_sub, map_sub, map_sub, map_sub,
    H (mult L) (inf_le_left.trans inf_le_left) haz, H (pullback.fst f f) (inf_le_left.trans inf_le_right) hbz,
    H (pullback.snd f f) inf_le_right hcz] at hmem
  exact hmem

end GoodReductionJacobian.RelativeGroupLaw.CutBody

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_affine_formallyUnramified_stalkMap_action_one.GoodReductionJacobian TopologicalSpace"

set_option maxHeartbeats 1600000 in
open GoodReductionJacobian.RelativeGroupLaw.CutBody CutAlg CutGeo IsLocalRing in
theorem solution
    (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) :
    h ≤ g ∧ ∃ (S' : Scheme.{u}) (j' : S' ⟶ G) (eS : Spec (CommRingCat.of k) ⟶ S')
      (heS : eS ≫ j' ≫ f = 𝟙 _),
      IsAffine S' ∧ SmoothOfRelativeDimension (g - h) (j' ≫ f) ∧
      ((pullback.map (i ≫ f) (j' ≫ f) (i ≫ f) f (𝟙 N) j' (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i).stalkMap
        (pullback.lift (LN.one (𝟙 _)).1 eS ((LN.one (𝟙 _)).2.trans heS.symm)
          (IsLocalRing.closedPoint k))).hom.FormallyUnramified := by
  classical

  set pt : ↑(Spec (CommRingCat.of k)) := closedPoint k with hpt
  set eG : Spec (CommRingCat.of k) ⟶ G := (L.one (𝟙 _)).1 with heG
  set eN : Spec (CommRingCat.of k) ⟶ N := (LN.one (𝟙 _)).1 with heN
  have heGf : eG ≫ f = 𝟙 _ := (L.one (𝟙 _)).2
  have heNf : eN ≫ i ≫ f = 𝟙 _ := (LN.one (𝟙 _)).2
  have heNi : eN ≫ i = eG := congrArg Subtype.val (comp_one_eq_one L i LN hi (𝟙 _))
  set xN : ↑N := eN.base pt with hxN
  set xG : ↑G := (eN ≫ i).base pt with hxG
  have hxG' : xG = eG.base pt := by rw [hxG, heNi]
  have hxGi : i.base xN = xG := rfl

  letI algP : Algebra k (G.presheaf.stalk xG) := stalkAlgebra f xG
  letI algQ : Algebra k (N.presheaf.stalk xN) := stalkAlgebra (i ≫ f) xN
  letI algPQ : Algebra (G.presheaf.stalk xG) (N.presheaf.stalk xN) := (i.stalkMap xN).hom.toAlgebra
  haveI : IsScalarTower k (G.presheaf.stalk xG) (N.presheaf.stalk xN) :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_comp_algebraMap f i xN).symm
  letI algQk : Algebra (N.presheaf.stalk xN) k := (Scheme.stalkClosedPointTo eN).hom.toAlgebra
  letI algPk : Algebra (G.presheaf.stalk xG) k := (Scheme.stalkClosedPointTo (eN ≫ i)).hom.toAlgebra
  haveI : IsScalarTower (G.presheaf.stalk xG) (N.presheaf.stalk xN) k :=
    IsScalarTower.of_algebraMap_eq' (by
      simp only [RingHom.algebraMap_toAlgebra, Scheme.stalkClosedPointTo_comp, CommRingCat.hom_comp]; rfl)
  haveI : IsScalarTower k (N.presheaf.stalk xN) k :=
    IsScalarTower.of_algebraMap_eq' (stalkClosedPointTo_comp_algebraMap (i ≫ f) eN heNf).symm
  haveI : IsScalarTower k (G.presheaf.stalk xG) k :=
    IsScalarTower.of_algebraMap_eq' (stalkClosedPointTo_comp_algebraMap f (eN ≫ i)
        (by rw [Category.assoc, heNf])).symm
  have hPQ : Function.Surjective (algebraMap (G.presheaf.stalk xG) (N.presheaf.stalk xN)) :=
    i.stalkMap_surjective xN
  obtain ⟨bP₀⟩ := nonempty_basis_kaehler_stalk f g xG
  obtain ⟨bQ₀⟩ := nonempty_basis_kaehler_stalk (i ≫ f) h xN
  obtain ⟨hhg, t, u, ht, hu, b, hbt, hbu⟩ := exists_adapted_coords hPQ
    (Algebra.TensorProduct.basis k bP₀) (Algebra.TensorProduct.basis k bQ₀)
  refine ⟨hhg, ?_⟩

  obtain ⟨V, hV, hxGV, hstd⟩ := exists_isStandardSmoothOfRelativeDimension_chart f g xG
  letI algA : Algebra k Γ(G, V) := secAlgebra f V
  letI algAP : Algebra Γ(G, V) (G.presheaf.stalk xG) := TopCat.Presheaf.algebra_section_stalk G.presheaf ⟨xG, hxGV⟩
  haveI : IsScalarTower k Γ(G, V) (G.presheaf.stalk xG) := isScalarTower_sec_stalk f V xG hxGV
  letI algAk : Algebra Γ(G, V) k :=
    ((Scheme.stalkClosedPointTo (eN ≫ i)).hom.comp (G.presheaf.germ V xG hxGV).hom).toAlgebra
  haveI : IsScalarTower Γ(G, V) (G.presheaf.stalk xG) k := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k Γ(G, V) k := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq Γ(G, V) (G.presheaf.stalk xG) k, RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq k Γ(G, V) (G.presheaf.stalk xG), ← IsScalarTower.algebraMap_eq k _ k])
  haveI hlocP : IsLocalization.AtPrime (G.presheaf.stalk xG) (hV.primeIdealOf ⟨xG, hxGV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨xG, hxGV⟩
  have hprime : (hV.primeIdealOf ⟨xG, hxGV⟩).asIdeal = RingHom.ker (algebraMap Γ(G, V) k) :=
    primeIdealOf_eq_ker (eN ≫ i) hV hxGV
  have hMk : ∀ s ∈ (hV.primeIdealOf ⟨xG, hxGV⟩).asIdeal.primeCompl, algebraMap Γ(G, V) k s ≠ 0 := by
    intro s hs
    have hs' := Ideal.mem_primeCompl_iff.mp hs
    rwa [hprime, RingHom.mem_ker] at hs'
  have hx0 : ∀ l, algebraMap (G.presheaf.stalk xG) k (Sum.elim t u l) = 0 := by
    rintro (l | l)
    · exact ht l
    · simp only [Sum.elim_inr]
      rw [IsScalarTower.algebraMap_apply _ (N.presheaf.stalk xN) k, hu l, map_zero]
  obtain ⟨a, s, hsM, has, b', hb'⟩ := exists_coords_of_isLocalization
    (hV.primeIdealOf ⟨xG, hxGV⟩).asIdeal.primeCompl hMk (Sum.elim t u) hx0 b (by
      rintro (l | l) <;> simp [hbt, hbu])
  have ha0 : ∀ l, algebraMap Γ(G, V) k (a l) = 0 := by
    intro l
    rw [IsScalarTower.algebraMap_apply _ (G.presheaf.stalk xG) k, has l, map_mul, hx0 l, mul_zero]

  obtain ⟨bΩ₀⟩ := nonempty_basis_kaehler_of_isStandardSmoothOfRelativeDimension (R := k) (S := Γ(G, V)) g
  let eι : Fin g ≃ Fin h ⊕ Fin (g - h) := (finCongr (by omega)).trans finSumFinEquiv.symm
  let bΩ : Module.Basis (Fin h ⊕ Fin (g - h)) Γ(G, V) (Ω[Γ(G, V)⁄k]) := bΩ₀.reindex eι
  set r : Γ(G, V) := bΩ.det (fun l => KaehlerDifferential.D k Γ(G, V) (a l)) with hr
  have hr0 : algebraMap Γ(G, V) k r ≠ 0 :=
    algebraMap_det_ne_zero_of_linearIndependent bΩ _ (by simpa [← hb'] using b'.linearIndependent)
  let A' : Type u := Localization.Away r
  have hrA' : IsUnit (algebraMap Γ(G, V) A' r) := IsLocalization.Away.algebraMap_isUnit r
  obtain ⟨bA'₀, hbA'₀⟩ := exists_basis_baseChange_of_isUnit_det bΩ _ A' hrA'
  obtain ⟨bA', hbA'⟩ := exists_basis_kaehler_of_isLocalization (k := k) (.powers r) a bA'₀ hbA'₀
  haveI : Algebra.IsStandardSmooth k Γ(G, V) := hstd.isStandardSmooth
  haveI : Algebra.Etale Γ(G, V) A' := Algebra.Etale.of_isLocalizationAway r
  haveI : Algebra.FinitePresentation k A' := Algebra.FinitePresentation.trans k Γ(G, V) A'
  haveI : Algebra.FormallySmooth k A' := Algebra.FormallySmooth.comp k Γ(G, V) A'

  have hEt := (etale_aeval_iff_of_equiv (k := k) Equiv.ulift
    (fun l : Fin h ⊕ Fin (g - h) => algebraMap Γ(G, V) A' (a l))).mp
    (Algebra.FormallySmooth.etale_aeval_of_basis_kaehlerDifferential (R := k) (A := A')
      (ι := ULift.{u} (Fin h ⊕ Fin (g - h))) _ (bA'.reindex Equiv.ulift.symm) (fun l => by
        simp [hbA']))
  set J : Ideal A' := Ideal.span (Set.range ((fun l : Fin h ⊕ Fin (g - h) => algebraMap Γ(G, V) A' (a l)) ∘ Sum.inl)) with hJ
  let C : Type u := A' ⧸ J
  have hSm : SmoothOfRelativeDimension (g - h) (Spec.map (CommRingCat.ofHom (algebraMap k C))) :=
    smoothOfRelativeDimension_SpecMap_quotient_of_etale_aeval _ hEt

  set εA : Γ(G, V) →+* k := algebraMap Γ(G, V) k with hεA
  let εA' : A' →+* k := IsLocalization.Away.lift r (g := εA) (isUnit_iff_ne_zero.mpr hr0)
  have hεA' : εA'.comp (algebraMap Γ(G, V) A') = εA := IsLocalization.Away.lift_comp r _
  have hJε : ∀ x ∈ J, εA' x = 0 := by
    intro x hx
    rw [← RingHom.mem_ker]
    refine (Ideal.span_le (I := RingHom.ker εA')).mpr ?_ hx
    rintro _ ⟨l, rfl⟩
    simp only [Function.comp_apply, RingHom.mem_ker, SetLike.mem_coe]
    rw [← RingHom.comp_apply, hεA']
    exact ha0 _
  let εC : C →+* k := Ideal.Quotient.lift J εA' hJε
  set q : Γ(G, V) →+* C := (Ideal.Quotient.mk J).comp (algebraMap Γ(G, V) A') with hq
  have hεCq : εC.comp q = εA := by
    rw [hq, ← RingHom.comp_assoc, Ideal.Quotient.lift_comp_mk]
    exact hεA'
  have hqk : q.comp (algebraMap k Γ(G, V)) = algebraMap k C := by
    rw [hq, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq k Γ(G, V) A']
    exact (IsScalarTower.algebraMap_eq k A' C).symm
  have hεCk : εC.comp (algebraMap k C) = RingHom.id k := by
    rw [← hqk, ← RingHom.comp_assoc, hεCq, hεA]
    exact (IsScalarTower.algebraMap_eq k Γ(G, V) k).symm

  let S' : Scheme.{u} := Spec (CommRingCat.of C)
  let j' : S' ⟶ G := Spec.map (CommRingCat.ofHom q) ≫ hV.fromSpec
  let eS : Spec (CommRingCat.of k) ⟶ S' := Spec.map (CommRingCat.ofHom εC)
  have hj'f : j' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k C)) := by
    change (Spec.map (CommRingCat.ofHom q) ≫ hV.fromSpec) ≫ f = _
    rw [Category.assoc, fromSpec_comp f hV, ← Spec.map_comp]
    congr 1
  have heS : eS ≫ j' ≫ f = 𝟙 _ := by
    rw [hj'f]
    change Spec.map (CommRingCat.ofHom εC) ≫ _ = _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    apply CommRingCat.hom_ext
    exact hεCk
  have heSj' : eS ≫ j' = eG := by
    change Spec.map (CommRingCat.ofHom εC) ≫ Spec.map (CommRingCat.ofHom q) ≫ hV.fromSpec = _
    rw [← Spec.map_comp_assoc, ← heNi, ← SpecMap_germ_stalkClosedPointTo_fromSpec (eN ≫ i) hV hxGV]
    congr 2
    apply CommRingCat.hom_ext
    exact hεCq
  refine ⟨S', j', eS, heS, inferInstance, hj'f ▸ hSm, ?_⟩

  set X := pullback (i ≫ f) (j' ≫ f) with hX
  set zt : Spec (CommRingCat.of k) ⟶ X := pullback.lift eN eS (heNf.trans heS.symm) with hzt
  set z : ↑X := zt.base pt with hz
  set act : X ⟶ G := pullback.map (i ≫ f) (j' ≫ f) (i ≫ f) f (𝟙 N) j' (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i with hact
  set ρ : X ⟶ pullback f f := pullback.map (i ≫ f) (j' ≫ f) f f i j' (𝟙 _) (Category.comp_id _)
      (Category.comp_id _) with hρ
  have hρm : ρ ≫ mult L = act := (map_comp_action_eq_map_comp_mul L i j').symm
  have hρ₁ : ρ ≫ pullback.fst f f = pullback.fst _ _ ≫ i := by rw [hρ, pullback.lift_fst]
  have hρ₂ : ρ ≫ pullback.snd f f = pullback.snd _ _ ≫ j' := by rw [hρ, pullback.lift_snd]
  have hzt₁ : zt ≫ pullback.fst _ _ = eN := by rw [hzt, pullback.lift_fst]
  have hzt₂ : zt ≫ pullback.snd _ _ = eS := by rw [hzt, pullback.lift_snd]
  have hztρ : zt ≫ ρ = pullback.lift eG eG (by rfl) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hρ₁, ← Category.assoc, hzt₁, heNi, pullback.lift_fst]
    · rw [Category.assoc, hρ₂, ← Category.assoc, hzt₂, heSj', pullback.lift_snd]
  have hρz : ρ.base z = (pullback.lift eG eG (by rfl)).base pt := by
    rw [← hztρ]; rfl
  have hz₁ : (pullback.fst (i ≫ f) (j' ≫ f)).base z = xN := by
    change (zt ≫ pullback.fst (i ≫ f) (j' ≫ f)).base pt = xN
    rw [hzt₁]
  have hzta : zt ≫ act = eG := by
    rw [← hρm, ← Category.assoc, hztρ, lift_one_one_comp_mult]
  have hz₁' : (pullback.fst (i ≫ f) (j' ≫ f) ≫ i).base z = xG := by
    change (zt ≫ pullback.fst (i ≫ f) (j' ≫ f) ≫ i).base pt = xG
    rw [← Category.assoc, hzt₁]
  have hz₂' : (pullback.snd (i ≫ f) (j' ≫ f) ≫ j').base z = xG := by
    change (zt ≫ pullback.snd (i ≫ f) (j' ≫ f) ≫ j').base pt = xG
    rw [← Category.assoc, hzt₂, heSj', ← hxG']
  have hza : act.base z = xG := by
    change (zt ≫ act).base pt = xG
    rw [hzta, ← hxG']
  change (act.stalkMap z).hom.FormallyUnramified

  have heV : (L.one (𝟙 (Spec (CommRingCat.of k)))).1.base (closedPoint k) ∈ V := hxG' ▸ hxGV
  have hzaV : act.base z ∈ V := hza ▸ hxGV
  have hz₁V : (pullback.fst (i ≫ f) (j' ≫ f) ≫ i).base z ∈ V := hz₁' ▸ hxGV
  have hz₂V : (pullback.snd (i ≫ f) (j' ≫ f) ≫ j').base z ∈ V := hz₂' ▸ hxGV

  have hj'V : j' ⁻¹ᵁ V = ⊤ := by
    change (Spec.map (CommRingCat.ofHom q) ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤
    rw [Scheme.Hom.comp_preimage, hV.fromSpec_preimage_self, Scheme.Hom.preimage_top]
  have hjapp : j'.appLE V ⊤ hj'V.ge = CommRingCat.ofHom q ≫ (Scheme.ΓSpecIso (.of C)).inv := by
    have e1 : (Spec.map (CommRingCat.ofHom q)).appLE ⊤ ⊤ (by simp) = (Spec.map (CommRingCat.ofHom q)).appTop :=
      (Scheme.Hom.app_eq_appLE _).symm
    change (Spec.map (CommRingCat.ofHom q) ≫ hV.fromSpec).appLE V ⊤ _ = _
    rw [Scheme.Hom.comp_appLE, hV.fromSpec_app_self, Category.assoc, Scheme.Hom.map_appLE, e1,
      Scheme.ΓSpecIso_inv_naturality]
    rfl
  have hqt : ∀ i', q (a (Sum.inl i')) = 0 := fun i' =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i', rfl⟩)
  have hiu0 : ∀ j, (N.presheaf.germ (i ⁻¹ᵁ V) xN hxGV).hom ((i.app V).hom (a (Sum.inr j))) = 0 := by
    intro j
    rw [← Scheme.Hom.germ_stalkMap_apply i V xN hxGV]
    change algebraMap (G.presheaf.stalk xG) (N.presheaf.stalk xN) (algebraMap Γ(G, V) (G.presheaf.stalk xG) (a (Sum.inr j))) = 0
    rw [has, map_mul]
    simp only [Sum.elim_inr, hu, mul_zero]

  haveI : IsNoetherianRing Γ(G, V) := Algebra.FiniteType.isNoetherianRing k _
  have hmG : ∀ (x₀ : ↑G) (hx₀ : x₀ = xG) (hx₀V : x₀ ∈ V), maximalIdeal (G.presheaf.stalk x₀) =
      Ideal.span (Set.range fun l => (G.presheaf.germ V x₀ hx₀V).hom (a l)) := by
    intro x₀ hx₀ hx₀V
    subst hx₀
    have h1 : maximalIdeal (G.presheaf.stalk xG) =
        (RingHom.ker (algebraMap Γ(G, V) k)).map (algebraMap Γ(G, V) (G.presheaf.stalk xG)) := by
      rw [← hprime]; exact (IsLocalization.AtPrime.map_eq_maximalIdeal _ _).symm
    have h2 : RingHom.ker (algebraMap Γ(G, V) k) ≤
        Ideal.span (Set.range a) ⊔ RingHom.ker (algebraMap Γ(G, V) k) ^ 2 :=
      ker_le_span_sup_sq (Set.range a) (by rintro _ ⟨l, rfl⟩; exact ha0 l) (by
        rw [← Set.range_comp]
        convert b'.span_eq using 2
        ext l; simp [hb'])
    have hgen : (fun l => (G.presheaf.germ V xG hx₀V).hom (a l)) =
        (algebraMap Γ(G, V) (G.presheaf.stalk xG)) ∘ a := rfl
    have hFG : (maximalIdeal (G.presheaf.stalk xG)).FG := by
      obtain ⟨S, hS⟩ := (IsNoetherian.noetherian (RingHom.ker (algebraMap Γ(G, V) k)) :)
      replace hS : Ideal.span (S : Set Γ(G, V)) = RingHom.ker (algebraMap Γ(G, V) k) := hS
      refine ⟨S.image (algebraMap Γ(G, V) (G.presheaf.stalk xG)), ?_⟩
      change Ideal.span _ = _
      rw [h1, Finset.coe_image, ← Ideal.map_span, hS]
    apply le_antisymm
    · apply Submodule.le_of_le_smul_of_le_jacobson_bot hFG (maximalIdeal_le_jacobson _)
      calc maximalIdeal (G.presheaf.stalk xG)
          = (RingHom.ker (algebraMap Γ(G, V) k)).map (algebraMap Γ(G, V) (G.presheaf.stalk xG)) := h1
        _ ≤ (Ideal.span (Set.range a) ⊔ RingHom.ker (algebraMap Γ(G, V) k) ^ 2).map
              (algebraMap Γ(G, V) (G.presheaf.stalk xG)) := Ideal.map_mono h2
        _ = Ideal.span (Set.range fun l => (G.presheaf.germ V xG hx₀V).hom (a l)) ⊔
              maximalIdeal (G.presheaf.stalk xG) • maximalIdeal (G.presheaf.stalk xG) := by
            rw [Ideal.map_sup, Ideal.map_span, Ideal.map_pow, ← h1, hgen, Set.range_comp, pow_two, Ideal.smul_eq_mul]
    · rw [Ideal.span_le]
      rintro _ ⟨l, rfl⟩
      change (G.presheaf.germ V xG hx₀V).hom (a l) ∈ maximalIdeal _
      rw [← ker_stalkClosedPointTo (eN ≫ i), RingHom.mem_ker]
      exact ha0 l

  let xv : Fin h ⊕ Fin (g - h) → G.presheaf.stalk (act.base z) := fun l => (G.presheaf.germ V _ hzaV).hom (a l)
  let yv : Fin h ⊕ Fin (g - h) → X.presheaf.stalk z := fun l => Sum.elim
    (fun i' => (X.presheaf.germ ((pullback.fst (i ≫ f) (j' ≫ f) ≫ i) ⁻¹ᵁ V) z hz₁V).hom
      (((pullback.fst (i ≫ f) (j' ≫ f) ≫ i).app V).hom (a (Sum.inl i'))))
    (fun j => (X.presheaf.germ ((pullback.snd (i ≫ f) (j' ≫ f) ≫ j') ⁻¹ᵁ V) z hz₂V).hom
      (((pullback.snd (i ≫ f) (j' ≫ f) ≫ j').app V).hom (a (Sum.inr j)))) l
  have hxv : ∀ l, xv l ∈ maximalIdeal _ := by
    intro l
    refine (germ_mem_maximalIdeal_iff_of_eq hza hzaV hxGV (a l)).mpr ?_
    rw [← ker_stalkClosedPointTo (eN ≫ i), RingHom.mem_ker]
    exact ha0 l

  have hy0u : ∀ j, (X.presheaf.germ ((pullback.fst (i ≫ f) (j' ≫ f) ≫ i) ⁻¹ᵁ V) z hz₁V).hom
      (((pullback.fst (i ≫ f) (j' ≫ f) ≫ i).app V).hom (a (Sum.inr j))) = 0 := by
    intro j
    change (X.presheaf.germ ((pullback.fst (i ≫ f) (j' ≫ f)) ⁻¹ᵁ (i ⁻¹ᵁ V)) z hz₁V).hom
      (((pullback.fst (i ≫ f) (j' ≫ f)).app (i ⁻¹ᵁ V)).hom ((i.app V).hom (a (Sum.inr j)))) = 0
    rw [← Scheme.Hom.germ_stalkMap_apply (pullback.fst (i ≫ f) (j' ≫ f)) (i ⁻¹ᵁ V) z hz₁V,
      (germ_eq_zero_iff_of_eq hz₁ hz₁V hxGV _).mpr (hiu0 j), map_zero]
  have hy0t : ∀ i', (X.presheaf.germ ((pullback.snd (i ≫ f) (j' ≫ f) ≫ j') ⁻¹ᵁ V) z hz₂V).hom
      (((pullback.snd (i ≫ f) (j' ≫ f) ≫ j').app V).hom (a (Sum.inl i'))) = 0 := by
    intro i'
    have key : ∀ (y : ↑S') (hy : y ∈ j' ⁻¹ᵁ V),
        j'.app V ≫ S'.presheaf.germ (j' ⁻¹ᵁ V) y hy =
          (CommRingCat.ofHom q ≫ (Scheme.ΓSpecIso (.of C)).inv) ≫ S'.presheaf.germ ⊤ y trivial := by
      intro y hy
      rw [← hjapp, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    change (X.presheaf.germ ((pullback.snd (i ≫ f) (j' ≫ f)) ⁻¹ᵁ (j' ⁻¹ᵁ V)) z hz₂V).hom
      (((pullback.snd (i ≫ f) (j' ≫ f)).app (j' ⁻¹ᵁ V)).hom ((j'.app V).hom (a (Sum.inl i')))) = 0
    have key' : (S'.presheaf.germ (j' ⁻¹ᵁ V) ((pullback.snd (i ≫ f) (j' ≫ f)).base z) hz₂V).hom
        ((j'.app V).hom (a (Sum.inl i'))) = 0 := by
      have := congrArg (fun φ : Γ(G, V) ⟶ _ => φ.hom (a (Sum.inl i'))) (key _ hz₂V)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, hqt, map_zero] at this
      exact this
    rw [← Scheme.Hom.germ_stalkMap_apply (pullback.snd (i ≫ f) (j' ≫ f)) (j' ⁻¹ᵁ V) z hz₂V]
    erw [key']
    exact map_zero _
  have hxy : ∀ l, (act.stalkMap z).hom (xv l) - yv l ∈ maximalIdeal _ ^ 2 := by
    intro l
    have hφ : (G.presheaf.germ V _ heV).hom (a l) ∈ maximalIdeal _ := by
      refine (germ_mem_maximalIdeal_iff_of_eq hxG' hxGV heV (a l)).mp ?_
      rw [← ker_stalkClosedPointTo (eN ≫ i), RingHom.mem_ker]
      exact ha0 l
    have H := germ_sub_sub_mem_sq L V heV ρ z hρz act _ _ hρm hρ₁ hρ₂ hzaV hz₁V hz₂V (a l) hφ
    change (act.stalkMap z).hom ((G.presheaf.germ V (act.base z) hzaV).hom (a l)) - yv l ∈ _
    rw [Scheme.Hom.germ_stalkMap_apply act V z hzaV]
    rcases l with i' | j
    · rw [hy0t i', sub_zero] at H
      exact H
    · rw [hy0u j, sub_zero] at H
      exact H
  have hyv : maximalIdeal (X.presheaf.stalk z) = Ideal.span (Set.range yv) := by
    apply le_antisymm
    · have hP := maximalIdeal_stalk_pullback_le (i ≫ f) (j' ≫ f) eN heNf eS heS z rfl
      refine hP.trans (sup_le ?_ ?_)
      · rw [← map_maximalIdeal_stalkMap_of_surjective i ((pullback.fst (i ≫ f) (j' ≫ f)).base z)
          (i.stalkMap_surjective _), hmG (i.base ((pullback.fst (i ≫ f) (j' ≫ f)).base z)) hz₁' hz₁V,
          Ideal.map_map, Ideal.map_span, Ideal.span_le]
        rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
        change ((pullback.fst (i ≫ f) (j' ≫ f)).stalkMap z).hom ((i.stalkMap ((pullback.fst (i ≫ f) (j' ≫ f)).base z)).hom
          ((G.presheaf.germ V (i.base ((pullback.fst (i ≫ f) (j' ≫ f)).base z)) hz₁V).hom (a l))) ∈ Ideal.span (Set.range yv)
        rw [Scheme.Hom.germ_stalkMap_apply i V ((pullback.fst (i ≫ f) (j' ≫ f)).base z) hz₁V,
          Scheme.Hom.germ_stalkMap_apply (pullback.fst (i ≫ f) (j' ≫ f)) (i ⁻¹ᵁ V) z hz₁V]
        rcases l with i' | j
        · exact Ideal.subset_span ⟨Sum.inl i', rfl⟩
        · rw [show (X.presheaf.germ ((pullback.fst (i ≫ f) (j' ≫ f)) ⁻¹ᵁ (i ⁻¹ᵁ V)) z hz₁V).hom
              (((pullback.fst (i ≫ f) (j' ≫ f)).app (i ⁻¹ᵁ V)).hom ((i.app V).hom (a (Sum.inr j)))) = 0 from hy0u j]
          exact Ideal.zero_mem _
      · haveI : SurjectiveOnStalks j' := by
          haveI : SurjectiveOnStalks (Spec.map (CommRingCat.ofHom q)) :=
            SurjectiveOnStalks.Spec_iff.mpr
              ((RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective).comp
                (RingHom.surjectiveOnStalks_of_isLocalization (.powers r) A'))
          exact inferInstance
        rw [← map_maximalIdeal_stalkMap_of_surjective j' ((pullback.snd (i ≫ f) (j' ≫ f)).base z)
          (j'.stalkMap_surjective _), hmG (j'.base ((pullback.snd (i ≫ f) (j' ≫ f)).base z)) hz₂' hz₂V,
          Ideal.map_map, Ideal.map_span, Ideal.span_le]
        rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
        change ((pullback.snd (i ≫ f) (j' ≫ f)).stalkMap z).hom ((j'.stalkMap ((pullback.snd (i ≫ f) (j' ≫ f)).base z)).hom
          ((G.presheaf.germ V (j'.base ((pullback.snd (i ≫ f) (j' ≫ f)).base z)) hz₂V).hom (a l))) ∈ Ideal.span (Set.range yv)
        rw [Scheme.Hom.germ_stalkMap_apply j' V ((pullback.snd (i ≫ f) (j' ≫ f)).base z) hz₂V,
          Scheme.Hom.germ_stalkMap_apply (pullback.snd (i ≫ f) (j' ≫ f)) (j' ⁻¹ᵁ V) z hz₂V]
        rcases l with i' | j
        · rw [show (X.presheaf.germ ((pullback.snd (i ≫ f) (j' ≫ f)) ⁻¹ᵁ (j' ⁻¹ᵁ V)) z hz₂V).hom
              (((pullback.snd (i ≫ f) (j' ≫ f)).app (j' ⁻¹ᵁ V)).hom ((j'.app V).hom (a (Sum.inl i')))) = 0 from hy0t i']
          exact Ideal.zero_mem _
        · exact Ideal.subset_span ⟨Sum.inr j, rfl⟩
    · rw [Ideal.span_le]
      rintro _ ⟨l, rfl⟩
      rcases l with i' | j
      · change (X.presheaf.germ _ z hz₁V).hom _ ∈ maximalIdeal _
        rw [← Scheme.Hom.germ_stalkMap_apply (pullback.fst (i ≫ f) (j' ≫ f) ≫ i) V z hz₁V]
        exact map_nonunit _ _ ((germ_mem_maximalIdeal_iff_of_eq (hz₁'.trans hxG') hz₁V heV _).mpr
          ((germ_mem_maximalIdeal_iff_of_eq hxG' hxGV heV _).mp (by
            rw [← ker_stalkClosedPointTo (eN ≫ i), RingHom.mem_ker]; exact ha0 _)))
      · change (X.presheaf.germ _ z hz₂V).hom _ ∈ maximalIdeal _
        rw [← Scheme.Hom.germ_stalkMap_apply (pullback.snd (i ≫ f) (j' ≫ f) ≫ j') V z hz₂V]
        exact map_nonunit _ _ ((germ_mem_maximalIdeal_iff_of_eq (hz₂'.trans hxG') hz₂V heV _).mpr
          ((germ_mem_maximalIdeal_iff_of_eq hxG' hxGV heV _).mp (by
            rw [← ker_stalkClosedPointTo (eN ≫ i), RingHom.mem_ker]; exact ha0 _)))

  letI algZ : Algebra k (X.presheaf.stalk z) := stalkAlgebra (act ≫ f) z
  letI algGz : Algebra k (G.presheaf.stalk (act.base z)) := stalkAlgebra f (act.base z)
  have hztf : zt ≫ act ≫ f = 𝟙 _ := by
    rw [← Category.assoc, hzta]; exact heGf
  have hk : Function.Surjective ((residue (X.presheaf.stalk z)).comp
      ((act.stalkMap z).hom.comp (algebraMap k (G.presheaf.stalk (act.base z))))) := by
    rw [stalkMap_comp_algebraMap f act z]
    exact residue_comp_algebraMap_surjective (act ≫ f) zt hztf
  haveI : LocallyOfFiniteType act := by
    have hactf : act ≫ f = pullback.fst (i ≫ f) (j' ≫ f) ≫ i ≫ f := by
      rw [hact, Category.assoc, L.action_over i]
      change _ ≫ pullback.snd (i ≫ f) f ≫ f = _
      rw [← Category.assoc, pullback.lift_snd, Category.assoc, ← pullback.condition]
    haveI : Smooth (j' ≫ f) := hj'f ▸ SmoothOfRelativeDimension.smooth (g - h) _
    haveI : Smooth (i ≫ f) := SmoothOfRelativeDimension.smooth h _
    haveI : LocallyOfFiniteType (act ≫ f) := by rw [hactf]; infer_instance
    exact locallyOfFiniteType_of_comp act f
  exact formallyUnramified_of_span_eq_maximalIdeal (act.stalkMap z).hom (LocallyOfFiniteType.stalkMap act z)
    (algebraMap k _) hk xv yv hxv hyv hxy

end S_GoodReductionJacobian_RelativeGroupLaw_exists_affine_formallyUnramified_stalkMap_action_one
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_affine_formallyUnramified_stalkMap_action_one (solution)
