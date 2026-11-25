-- Prove2me | solution 1 for GlobalTheory.finEtale_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:42:59.949254+00:00
-- url     : https://prove2.me/submissions/99028105-90ac-4a2f-8055-c391efc4d5e1

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinEtaleFormallyUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj in
open scoped CategoryTheory.Obj CategoryTheory.MonObj in
attribute [local instance] Over.cartesianMonoidalCategory in
private theorem exists_algHom_apply_ne_zero_of_pointDerivation_eq_zero {C B : Type} [Field C] [IsAlgClosed C]
    [CommRing B] [Algebra C B] [FiniteDimensional C B]
    (hder : ∀ (φ : B →ₐ[C] C) (D : B →ₗ[C] C),
      (∀ a b, D (a * b) = φ a * D b + φ b * D a) → D = 0)
    {y : B} (hy : y ≠ 0) : ∃ φ : B →ₐ[C] C, φ y ≠ 0 := by
  classical
  set I : Ideal B := LinearMap.ker (LinearMap.mulRight B y) with hI
  have hItop : I ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ I := h ▸ Submodule.mem_top
    apply hy
    simpa [hI] using h1
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hItop
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.IsIntegral C (B ⧸ m) := Algebra.IsIntegral.of_finite C (B ⧸ m)
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := C) (K := B ⧸ m)
  let e := AlgEquiv.ofBijective (Algebra.ofId C (B ⧸ m)) hbij
  let φ : B →ₐ[C] C := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ C m)
  have hφ : ∀ b, φ b = 0 ↔ b ∈ m := by
    intro b
    simp [φ, Ideal.Quotient.eq_zero_iff_mem]
  have hφa : ∀ b, b - algebraMap C B (φ b) ∈ m := by
    intro b
    rw [← hφ, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  refine ⟨φ, fun hy0 => ?_⟩
  have hym : y ∈ m := (hφ y).1 hy0
  have hmm : m ≤ m * m := by
    intro x hx
    by_contra hx2
    obtain ⟨ℓ, hℓx, hℓ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
      (p := (m * m).restrictScalars C) hx2 inferInstance
    have hℓ0 : ∀ z ∈ m * m, ℓ z = 0 := by
      intro z hz
      have hmem := Submodule.mem_map_of_mem (f := ℓ)
        (show z ∈ (m * m).restrictScalars C from hz)
      rw [hℓ] at hmem
      exact (Submodule.mem_bot C).1 hmem
    let D : B →ₗ[C] C := ℓ.comp (LinearMap.id - (Algebra.linearMap C B).comp φ.toLinearMap)
    have hDapp : ∀ b, D b = ℓ (b - algebraMap C B (φ b)) := fun b => rfl
    have hD : ∀ a b, D (a * b) = φ a * D b + φ b * D a := by
      intro a b
      have key : a * b - algebraMap C B (φ (a * b)) =
          φ a • (b - algebraMap C B (φ b)) + φ b • (a - algebraMap C B (φ a)) +
            (a - algebraMap C B (φ a)) * (b - algebraMap C B (φ b)) := by
        rw [map_mul, map_mul, Algebra.smul_def, Algebra.smul_def]
        ring
      rw [hDapp, hDapp, hDapp, key, map_add, map_add, map_smul, map_smul,
        hℓ0 _ (Ideal.mul_mem_mul (hφa a) (hφa b)), smul_eq_mul, smul_eq_mul, add_zero]
    have hD0 := hder φ D hD
    apply hℓx
    have h2 : D x = ℓ x := by
      rw [hDapp, (hφ x).2 hx, map_zero, sub_zero]
    rw [← h2, hD0, LinearMap.zero_apply]
  haveI : IsNoetherianRing B := isNoetherian_of_tower C inferInstance
  have hidem : IsIdempotentElem m := le_antisymm Ideal.mul_le_left hmm
  obtain ⟨e', _he', hme⟩ := (Ideal.isIdempotentElem_iff_of_fg m (IsNoetherian.noetherian m)).1 hidem
  have he'm : e' ∈ m := hme ▸ Submodule.mem_span_singleton_self e'
  have hyspan : y ∈ B ∙ e' := hme ▸ hym
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.1 hyspan
  have hey : e' * y = y := by
    rw [← hz, smul_eq_mul, ← _root_.mul_assoc, mul_comm e' z, _root_.mul_assoc, _he'.eq]
  have h1e : 1 - e' ∈ m := hIm (by
    rw [hI, LinearMap.mem_ker, LinearMap.mulRight_apply, sub_mul, _root_.one_mul, hey, sub_self])
  exact hm.ne_top ((Ideal.eq_top_iff_one m).2 (by simpa using m.add_mem h1e he'm))
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj in
open scoped CategoryTheory.Obj CategoryTheory.MonObj in
attribute [local instance] Over.cartesianMonoidalCategory in
private theorem finrank_eq_card_algHom_of_pointDerivation_eq_zero {C B : Type} [Field C] [IsAlgClosed C]
    [CommRing B] [Algebra C B] [FiniteDimensional C B]
    (hder : ∀ (φ : B →ₐ[C] C) (D : B →ₗ[C] C),
      (∀ a b, D (a * b) = φ a * D b + φ b * D a) → D = 0) :
    Finite (B →ₐ[C] C) ∧ Module.finrank C B = Nat.card (B →ₐ[C] C) := by
  classical
  haveI hfin : Finite (B →ₐ[C] C) :=
    (linearIndependent_algHom_toLinearMap C B C).finite_of_isNoetherian
  refine ⟨hfin, le_antisymm ?_ (card_algHom_le_finrank C B C)⟩
  letI := Fintype.ofFinite (B →ₐ[C] C)
  let ev : B →ₗ[C] ((B →ₐ[C] C) → C) := LinearMap.pi fun φ => φ.toLinearMap
  have hev : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    by_contra hb0
    obtain ⟨φ, hφ⟩ := exists_algHom_apply_ne_zero_of_pointDerivation_eq_zero hder hb0
    exact hφ (congrFun hb φ)
  calc Module.finrank C B ≤ Module.finrank C ((B →ₐ[C] C) → C) :=
        LinearMap.finrank_le_finrank_of_injective hev
    _ = Nat.card (B →ₐ[C] C) := by
        rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]
end GlobalTheory
end

set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    (∀ (C O A : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) [CommRing O]
      [Algebra O C], v.Integers O →
      ∀ [CommRing A] [Algebra O A] [Module.Free O A] [Module.Finite O A],
      (∀ φ φ' : A →ₐ[O] DualNumber C, (∀ a, (φ a).fst = (φ' a).fst) → φ = φ') →
      Finite (A →ₐ[O] O) ∧ (∀ f : A, (∀ φ : A →ₐ[O] O, φ f = 0) → f = 0) ∧
        Module.finrank O A = Nat.card (A →ₐ[O] O)) := by
  intro C O A _ _ v _ _ hv _ _ _ _ hpts
  classical
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have hder : ∀ (φ : C ⊗[O] A →ₐ[C] C) (D : C ⊗[O] A →ₗ[C] C),
      (∀ a b, D (a * b) = φ a * D b + φ b * D a) → D = 0 := by
    intro φ D hD
    have hD1 : D 1 = 0 := by
      have h11 := hD 1 1
      rw [_root_.mul_one, map_one φ, _root_.one_mul] at h11
      linear_combination -h11
    let L : C ⊗[O] A →ₗ[C] DualNumber C :=
      (Algebra.linearMap C (DualNumber C)).comp φ.toLinearMap + (TrivSqZeroExt.inrHom C C).comp D
    have hLfst : ∀ b, (L b).fst = φ b := by
      intro b; simp [L, TrivSqZeroExt.algebraMap_eq_inl]
    have hLsnd : ∀ b, (L b).snd = D b := by
      intro b; simp [L, TrivSqZeroExt.algebraMap_eq_inl]
    let F : C ⊗[O] A →ₐ[C] DualNumber C := AlgHom.ofLinearMap L
      (TrivSqZeroExt.ext (by rw [hLfst, map_one]; rfl) (by rw [hLsnd, hD1]; rfl))
      (fun a b => TrivSqZeroExt.ext (by rw [TrivSqZeroExt.fst_mul, hLfst, hLfst, hLfst, map_mul])
        (by
          rw [TrivSqZeroExt.snd_mul, hLsnd, hLsnd, hLsnd, hLfst, hLfst, hD, smul_eq_mul,
            MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
          ring))
    let χ₁ : A →ₐ[O] DualNumber C := (F.restrictScalars O).comp Algebra.TensorProduct.includeRight
    let χ₀ : A →ₐ[O] DualNumber C :=
      (((Algebra.ofId C (DualNumber C)).comp φ).restrictScalars O).comp
        Algebra.TensorProduct.includeRight
    have hχ : χ₁ = χ₀ := hpts χ₁ χ₀ (fun a => by
      show (L _).fst = _
      rw [hLfst]
      rfl)
    have hDA : ∀ a : A, D ((1 : C) ⊗ₜ[O] a) = 0 := by
      intro a
      have h1 := congrArg TrivSqZeroExt.snd (DFunLike.congr_fun hχ a)
      change (L ((1 : C) ⊗ₜ[O] a)).snd =
        (algebraMap C (DualNumber C) (φ ((1 : C) ⊗ₜ[O] a))).snd at h1
      rw [hLsnd, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl] at h1
      exact h1
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c a =>
      have hca : c ⊗ₜ[O] a = c • ((1 : C) ⊗ₜ[O] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [hca, map_smul, hDA, smul_zero, LinearMap.zero_apply]
    | add x y hx hy => simp only [map_add, hx, hy, LinearMap.zero_apply, add_zero]
  obtain ⟨_, hrankB⟩ := finrank_eq_card_algHom_of_pointDerivation_eq_zero hder
  let Ψ : (A →ₐ[O] O) → (C ⊗[O] A →ₐ[C] C) := fun ψ =>
    Algebra.TensorProduct.lift (Algebra.ofId C C) ((Algebra.ofId O C).comp ψ)
      (fun _ _ => Commute.all _ _)
  have hΨapp : ∀ ψ a, Ψ ψ ((1 : C) ⊗ₜ[O] a) = algebraMap O C (ψ a) := by
    intro ψ a; simp [Ψ]
  have hΨ : Function.Bijective Ψ := by
    refine ⟨fun ψ₁ ψ₂ h => AlgHom.ext fun a => hinj (by rw [← hΨapp, ← hΨapp, h]), fun φ => ?_⟩
    let φA : A →ₐ[O] C := (φ.restrictScalars O).comp Algebra.TensorProduct.includeRight
    have hmem : ∀ a, φA a ∈ (Algebra.ofId O C).range := by
      intro a
      have hint : IsIntegral O (φA a) := (Algebra.IsIntegral.isIntegral a).map φA
      obtain ⟨x, hx⟩ := hv.exists_of_le_one (hv.mem_of_integral hint)
      exact ⟨x, hx⟩
    let eO := AlgEquiv.ofInjective (Algebra.ofId O C) hinj
    refine ⟨eO.symm.toAlgHom.comp (φA.codRestrict _ hmem), ?_⟩
    apply Algebra.TensorProduct.ext (AlgHom.ext fun c => (AlgHom.commutes _ c).trans (AlgHom.commutes _ c).symm)
    refine AlgHom.ext fun a => ?_
    show Ψ _ ((1 : C) ⊗ₜ[O] a) = φ ((1 : C) ⊗ₜ[O] a)
    rw [hΨapp]
    show algebraMap O C (eO.symm ⟨φA a, hmem a⟩) = φA a
    have h1 := congrArg Subtype.val (eO.apply_symm_apply ⟨φA a, hmem a⟩)
    exact h1
  haveI hfinA : Finite (A →ₐ[O] O) := Finite.of_injective Ψ hΨ.1
  refine ⟨hfinA, fun f hf => ?_, ?_⟩
  · have h1 : (1 : C) ⊗ₜ[O] f = 0 := by
      by_contra hne
      obtain ⟨φ, hφ⟩ := exists_algHom_apply_ne_zero_of_pointDerivation_eq_zero hder hne
      obtain ⟨ψ, rfl⟩ := hΨ.2 φ
      apply hφ
      rw [hΨapp, hf ψ, map_zero]
    have hflat : Function.Injective ((Algebra.linearMap O C).rTensor A) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hinj
    have h2 : ((Algebra.linearMap O C).rTensor A) ((1 : O) ⊗ₜ[O] f) = 0 := by
      rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
      exact h1
    have h3 : (1 : O) ⊗ₜ[O] f = 0 := hflat (by rw [h2, map_zero])
    simpa using congrArg (TensorProduct.lid O A) h3
  · haveI : Nontrivial O := (algebraMap O C).domain_nontrivial
    rw [← Module.finrank_baseChange (R := C), hrankB, Nat.card_eq_of_bijective Ψ hΨ]
end _root_.GlobalTheory
end GlobalTheory
