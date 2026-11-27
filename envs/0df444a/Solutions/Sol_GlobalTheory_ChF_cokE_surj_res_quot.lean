-- Prove2me | solution 1 for GlobalTheory.ChF.cokE_surj_res_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:34:20.5808+00:00
-- url     : https://prove2.me/submissions/5f9c287b-1fe9-4403-8d32-30a2bbb159ae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EigenbasisRestrictionSurjectiveEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PadicIntAlgebraOfIsAdicCompleteMatrixUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DualNumberPointPreimageTopOfReduction
import Theorems.Thm_GlobalTheory_ChF_eigB_res_surjective
import Theorems.Thm_GlobalTheory_ChF_padicInt_algebra_of_isAdicComplete_and_matrix_unique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_add
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
private lemma dualNumberPoint_preimage_top_of_reduction {O : Type} [CommRing O] {d r g m : ℕ} (A : Matrix (Fin d) (Fin r) O)
    (B : Matrix (Fin g) (Fin d) O) (h : SplitEx A B) (s : Fin m → Fin d → O)
    (hT : ∀ i, ∃ k, Aᵀ *ᵥ s k = Pi.single i 1) (f : Fin d → O) :
    ∃ (t : Fin d → O) (l : Fin g → O), t ∈ Submodule.span O (Set.range s) ∧ f = t + Bᵀ *ᵥ l := by
  obtain ⟨-, A', B', -, -, h3⟩ := h
  choose k hk using hT
  set t : Fin d → O := ∑ i, (Aᵀ *ᵥ f) i • s (k i) with ht
  have h0 : Aᵀ *ᵥ (f - t) = 0 := by
    rw [Matrix.mulVec_sub, ht, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hk]
    rw [sub_eq_zero]
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : (A * A' + B' * B)ᵀ *ᵥ (f - t) = f - t := by rw [h3]; simp
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero, zero_add] at h1
  refine ⟨t, B'ᵀ *ᵥ (f - t), ?_, by rw [h1]; abel⟩
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k i, rfl⟩)
private lemma idem_fix {O E : Type} [CommRing O] {g m : ℕ} (ρ : E → Matrix (Fin g) (Fin g) O)
    (ε : Fin m → Matrix (Fin g) (Fin g) O) (sg : Fin m → E → O)
    (horth : ∀ i j, ε i * ε j = if i = j then ε i else 0) (hsum : ∑ i, ε i = 1)
    (heig : ∀ a i, ρ a * ε i = sg i a • ε i) (i : Fin m)
    (hd : ∀ j, i ≠ j → ∃ a, IsUnit (sg i a - sg j a)) (y : Fin g → O)
    (hy : ∀ a, ρ a *ᵥ y = sg i a • y) : ε i *ᵥ y = y := by
  have hl : ∀ a j, ε j * ρ a = sg j a • ε j := by
    intro a j
    have : ρ a = ∑ k, sg k a • ε k := by
      rw [← Matrix.mul_one (ρ a), ← hsum, Matrix.mul_sum]
      simp only [heig]
    rw [this, Matrix.mul_sum]
    simp only [Matrix.mul_smul, horth]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · simp
  have hz : ∀ j, i ≠ j → ε j *ᵥ y = 0 := by
    intro j hj
    obtain ⟨a, ha⟩ := hd j hj
    have h1 : ε j *ᵥ (ρ a *ᵥ y) = sg j a • (ε j *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, hl, Matrix.smul_mulVec]
    rw [hy, Matrix.mulVec_smul] at h1
    have h2 : (sg i a - sg j a) • (ε j *ᵥ y) = 0 := by rw [sub_smul, h1, sub_self]
    exact (ha.smul_eq_zero).1 h2
  have h3 : (∑ j, ε j) *ᵥ y = y := by rw [hsum]; simp
  rw [Matrix.sum_mulVec, Finset.sum_eq_single i] at h3
  · exact h3
  · intro b _ hb
    exact hz b hb.symm
  · simp
end GlobalTheory.ChF
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ (U : UnramData p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp H) (i : Fin U.m) (τ : OE →+* O), (∀ x, U.sg i x = tauExt τ x) → ∀ (n : ℕ) (W : Fin n → Fin d → O), EigB ρG τ W → ∃ f : cokE H.Ht U.εT U.εL i (U.cj i) →ₗ[O] ((Fin n → O) ⧸ Submodule.span O (Set.range fun k => Pdiv.ChartF.res W (s k))), Function.Surjective f := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp _ g H d r m A B ρG N s hL U i τ hτ n W hW
  have hsurj := (GlobalTheory.ChF.eigB_res_surjective C v O hv OE d n ρG τ W hW).1
  have hZ : ∀ c : ℤ_[p], H.ρL (c ⊗ₜ[ℤ] (1 : OE)) = algebraMap ℤ_[p] O c • 1 := fun c =>
    (GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique p O).2 g (H.ρL.comp Algebra.TensorProduct.includeLeftRingHom) c
  have hy : ∀ l x, H.ρL x *ᵥ (B *ᵥ W l) = U.sg i x • (B *ᵥ W l) := by
    intro l x
    rw [hτ]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, Matrix.add_mulVec, hx, hy, add_smul]
    | tmul c a =>
      have e : (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = (c ⊗ₜ[ℤ] (1 : OE)) * ((1 : ℤ_[p]) ⊗ₜ[ℤ] a) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      have e2 : tauExt τ (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = algebraMap ℤ_[p] O c * τ a := by
        simp [tauExt, Algebra.ofId_apply]
      rw [e2, e, map_mul, hZ, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mulVec, Matrix.mulVec_mulVec,
        ← hL.eqB, ← Matrix.mulVec_mulVec, hW.1, Matrix.mulVec_smul, mul_smul]
  have hfix : ∀ l, U.εL i *ᵥ (B *ᵥ W l) = B *ᵥ W l := fun l =>
    idem_fix (fun x => H.ρL x) U.εL (fun j x => U.sg j x) U.εL_orth U.εL_sum U.εL_eig i
      (fun j hj => by
        obtain ⟨a, ha⟩ := U.distinct i j hj
        exact ⟨a, hv.isUnit_of_one' ha⟩) _ (hy l)
  have hres : ∀ l : Fin g → O, Pdiv.ChartF.res W (Bᵀ *ᵥ ((U.εL i)ᵀ *ᵥ l)) = Pdiv.ChartF.res W (Bᵀ *ᵥ l) := by
    intro l
    ext k
    change W k ⬝ᵥ (Bᵀ *ᵥ ((U.εL i)ᵀ *ᵥ l)) = W k ⬝ᵥ (Bᵀ *ᵥ l)
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      hfix, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  set S : Submodule O (Fin n → O) := Submodule.span O (Set.range fun k => Pdiv.ChartF.res W (s k)) with hS
  have hSm : ∀ t ∈ Submodule.span O (Set.range s), Pdiv.ChartF.res W t ∈ S := by
    intro t ht
    have := Submodule.mem_map_of_mem (f := Pdiv.ChartF.res W) ht
    rwa [Submodule.map_span, ← Set.range_comp] at this
  let F : LinearMap.range (Matrix.mulVecLin (U.εL i)ᵀ) →ₗ[O] ((Fin n → O) ⧸ S) :=
    S.mkQ ∘ₗ Pdiv.ChartF.res W ∘ₗ Matrix.mulVecLin Bᵀ ∘ₗ Submodule.subtype _
  have hF : ∀ x, F x = S.mkQ (Pdiv.ChartF.res W (Bᵀ *ᵥ x.1)) := fun x => rfl
  refine ⟨Submodule.liftQ _ F ?_, ?_⟩
  · rintro x ⟨ν, -, hx⟩
    rw [LinearMap.mem_ker, hF, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    apply hSm
    have hx' : x.1 = ∑ c, ν c • (fun l => H.Ht l c) := by
      have : H.Ht *ᵥ ν = x.1 := hx
      rw [← this]
      ext l
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [hx', Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    obtain ⟨k, hk⟩ := hL.fromB c
    rw [Matrix.mulVec_smul, ← hk]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · intro z
    obtain ⟨z, rfl⟩ := S.mkQ_surjective z
    obtain ⟨f, rfl⟩ := hsurj z
    obtain ⟨t, l, ht, rfl⟩ := dualNumberPoint_preimage_top_of_reduction A B hL.exact s hL.fromT f
    refine ⟨Submodule.Quotient.mk ⟨(U.εL i)ᵀ *ᵥ l, l, rfl⟩, ?_⟩
    rw [Submodule.liftQ_apply, hF, hres, map_add, map_add]
    have : S.mkQ (Pdiv.ChartF.res W t) = 0 := (Submodule.Quotient.mk_eq_zero S).2 (hSm t ht)
    rw [this, zero_add]
end GlobalTheory.ChF
