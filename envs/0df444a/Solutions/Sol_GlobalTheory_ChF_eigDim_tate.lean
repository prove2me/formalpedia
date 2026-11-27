-- Prove2me | solution 1 for GlobalTheory.ChF.eigDim_tate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:24:33.911436+00:00
-- url     : https://prove2.me/submissions/62a35c74-7489-4c65-b58b-dce4db7cbd74

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EigenspaceDimAddSplitExactTransposeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateModuleEigenspaceDimEqLieAlgebraSum
import Theorems.Thm_GlobalTheory_ChF_splitEx_one
import Theorems.Thm_GlobalTheory_T_eigenspaceDim_add_split_exact_transpose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
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
private theorem td_mem {C OE κ : Type} [Field C] [CommRing OE] [Fintype κ] [DecidableEq κ]
    (ρ : OE → Matrix κ κ C) (τ : OE →+* C) (x : κ → C) :
    x ∈ (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap C C))) (τ a)) ↔
      ∀ a, ρ a *ᵥ x = τ a • x := by
  simp [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
private theorem td_reindex {C OE κ κ' : Type} [Field C] [CommRing OE] [Fintype κ] [DecidableEq κ]
    [Fintype κ'] [DecidableEq κ'] (e : κ' ≃ κ) (ρ : OE → Matrix κ κ C) (τ : OE →+* C) :
    eigDim C (fun a => (ρ a).submatrix e e) τ = eigDim C ρ τ := by
  unfold eigDim
  rw [← LinearEquiv.finrank_map_eq (LinearEquiv.funCongrLeft C C e)
    (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap C C))) (τ a))]
  refine congrArg (fun S : Submodule C _ => Module.finrank C ↥S) ?_
  ext x
  rw [Submodule.mem_map_equiv, td_mem (fun a => (ρ a).submatrix e e), td_mem ρ]
  refine forall_congr' fun a => ?_
  rw [Matrix.submatrix_mulVec_equiv]
  have hx : (LinearEquiv.funCongrLeft C C e).symm x = x ∘ e.symm := by
    ext i; simp
  rw [hx]
  constructor
  · intro h
    ext i
    have := congrFun h (e.symm i)
    simpa using this
  · intro h
    ext i
    have := congrFun h (e i)
    simpa using this
private theorem td_base {C O OE κ : Type} [Field C] [CommRing O] [Algebra O C] [CommRing OE] [Fintype κ]
    [DecidableEq κ] (ρ : OE → Matrix κ κ O) (τ : OE →+* C) :
    eigDim C ρ τ = eigDim C (fun a => (ρ a).map (algebraMap O C)) τ := by
  rfl
private theorem td_twist {C OE κ : Type} [Field C] [CommRing OE] [Fintype κ]
    [DecidableEq κ] (ρ : OE → Matrix κ κ C) (τ : OE →+* C) (s : OE →+* OE) (hs : ∀ a, s (s a) = a) :
    eigDim C (fun a => ρ (s a)) τ = eigDim C ρ (τ.comp s) := by
  unfold eigDim
  refine congrArg (fun S : Submodule C _ => Module.finrank C ↥S) ?_
  ext x
  rw [td_mem (fun a => ρ (s a)), td_mem ρ]
  constructor
  · intro h a
    have := h (s a)
    rw [hs] at this
    simpa using this
  · intro h a
    have := h (s a)
    simpa [hs] using this
private theorem td_field {C OE : Type} [Field C] [IsAlgClosed C] [CharZero C] [CommRing OE] [IsDomain OE]
    [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] {g : ℕ}
    (ρ : OE →+* Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) C) (L : OE →+* Matrix (Fin g) (Fin g) C)
    (s : OE →+* OE) (hs : ∀ a, s (s a) = a) (E : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) C)
    (hE : IsUnit E.det) (hinv : ∀ a, (ρ a)ᵀ * E = E * ρ (s a))
    (H B : Matrix (Fin g) (Fin g ⊕ Fin g) C) (hH : ∀ a, H * ρ a = (L (s a))ᵀ * H) (c : C) (hc : c ≠ 0)
    (hform : Bᵀ * H - Hᵀ * B = c • E) (τ : OE →+* C) :
    eigDim C ρ τ = eigDim C L τ + eigDim C L (τ.comp s) := by
  set A : Matrix (Fin g ⊕ Fin g) (Fin g) C := E⁻¹ * Hᵀ with hA
  set A' : Matrix (Fin g) (Fin g ⊕ Fin g) C := (-c⁻¹) • B with hA'
  set B' : Matrix (Fin g ⊕ Fin g) (Fin g) C := c⁻¹ • (E⁻¹ * Bᵀ) with hB'
  have h1 : A * A' + B' * H = 1 := by
    have : A * A' + B' * H = c⁻¹ • (E⁻¹ * (Bᵀ * H - Hᵀ * B)) := by
      simp only [hA, hA', hB', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_sub, smul_sub,
        neg_smul, Matrix.mul_neg]
      abel
    rw [this, hform, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hE, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h2 : Matrix.fromRows A' H * Matrix.fromCols A B' = 1 := by
    rw [← Matrix.fromCols_mul_fromRows_eq_one_comm (Equiv.refl _), Matrix.fromCols_mul_fromRows, h1]
  rw [Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h2
  obtain ⟨h21, -, h23, h24⟩ := h2
  have hρA : ∀ a, ρ a * A = A * L a := by
    intro a
    have e1 : ρ a * E⁻¹ = E⁻¹ * (ρ (s a))ᵀ := by
      have := hinv (s a)
      rw [hs] at this
      calc ρ a * E⁻¹ = E⁻¹ * (E * ρ a) * E⁻¹ := by
            rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hE, Matrix.one_mul]
        _ = E⁻¹ * (ρ (s a))ᵀ * (E * E⁻¹) := by rw [← this]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_nonsing_inv _ hE, Matrix.mul_one]
    have e2 := congrArg Matrix.transpose (hH (s a))
    rw [hs, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at e2
    rw [hA, ← Matrix.mul_assoc, e1, Matrix.mul_assoc, e2, Matrix.mul_assoc]
  let e : Fin (g + g) ≃ Fin g ⊕ Fin g := finSumFinEquiv.symm
  let ρ' : OE →+* Matrix (Fin (g + g)) (Fin (g + g)) C :=
    (Matrix.reindexAlgEquiv C C e.symm).toRingEquiv.toRingHom.comp ρ
  have hρ' : ∀ a, ρ' a = (ρ a).submatrix e e := fun a => rfl
  let LT : OE →+* Matrix (Fin g) (Fin g) C :=
    { toFun := fun a => (L (s a))ᵀ
      map_one' := by simp
      map_mul' := fun a b => by rw [mul_comm a b, map_mul, map_mul, Matrix.transpose_mul]
      map_zero' := by simp
      map_add' := fun a b => by simp }
  have hsp : SplitEx (A.submatrix e id) (H.submatrix id e) := by
    refine ⟨?_, A'.submatrix id e, B'.submatrix e id, ?_, ?_, ?_⟩
    · rw [Matrix.submatrix_mul_equiv, h23]; simp
    · rw [Matrix.submatrix_mul_equiv, h21]; simp
    · rw [Matrix.submatrix_mul_equiv, h24]; simp
    · rw [← Matrix.submatrix_one_equiv e, ← h1]
      ext i j
      simp [Matrix.mul_apply]
  have k1 := (GlobalTheory.T.eigenspaceDim_add_split_exact_transpose C C OE (g + g) g g _ _ hsp ρ' L LT
    (fun a => by
      rw [hρ', Matrix.submatrix_mul_equiv, hH]
      ext i j
      simp [Matrix.mul_apply, LT])
    (fun a => by
      rw [hρ', Matrix.submatrix_mul_equiv, hρA]
      ext i j
      simp [Matrix.mul_apply]) τ).1
  let Z : OE →+* Matrix (Fin 0) (Fin 0) C :=
    { toFun := fun _ => 0
      map_one' := Subsingleton.elim _ _
      map_mul' := fun _ _ => Subsingleton.elim _ _
      map_zero' := rfl
      map_add' := fun _ _ => Subsingleton.elim _ _ }
  have k2 := (GlobalTheory.T.eigenspaceDim_add_split_exact_transpose C C OE g g 0 _ _ (splitEx_one g) (L.comp s) (L.comp s) Z
    (fun a => Subsingleton.elim _ _) (fun a => by simp) τ).2
  have k3 : eigDim C ρ' τ = eigDim C ρ τ := td_reindex e ρ τ
  have k4 : eigDim C LT τ = eigDim C L (τ.comp s) := k2.trans (td_twist L τ s hs)
  rw [← k3, k1, k4]
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
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (τ : OE →+* C), eigDim C (fun a : OE => (H.ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)) τ = eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) τ + eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) (τ.comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hU g H τ
  let j : OE →+* ℤ_[p] ⊗[ℤ] OE := (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := OE)).toRingHom
  let f : ℤ_[p] →+* C := (algebraMap O C).comp (algebraMap ℤ_[p] O)
  let s : OE →+* OE := ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom
  have hs : ∀ a, s (s a) = a := fun a => star_star a
  have hj : ∀ a, sigE p OE (j a) = j (s a) := fun a => rfl
  let ρ : OE →+* Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) C := (f.mapMatrix.comp H.ρ.toRingHom).comp j
  let L : OE →+* Matrix (Fin g) (Fin g) C := ((algebraMap O C).mapMatrix.comp H.ρL).comp j
  have hρ : ∀ a, ρ a = (H.ρ (j a)).map f := fun a => rfl
  have hL : ∀ a, L a = (H.ρL (j a)).map (algebraMap O C) := fun a => rfl
  have hc : algebraMap O C cp ≠ 0 := by
    intro h
    have h1 := hU.cp_val
    have h2 : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
    rw [h, map_zero, zero_pow h2] at h1
    exact hU.p_ne h1.symm
  have key := td_field ρ L s hs (H.E.map f)
    (by
      have := H.isUnit_det_E.map f
      rwa [RingHom.map_det, RingHom.mapMatrix_apply] at this)
    (fun a => by
      rw [hρ, hρ, ← hj, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, H.E_equivariant])
    (H.Ht.map (algebraMap O C)) (H.Bt.map (algebraMap O C))
    (fun a => by
      have := congrArg (fun M => M.map (algebraMap O C)) (H.Ht_equivariant.1 (j a))
      simp only [Matrix.map_mul, Matrix.transpose_map] at this
      rw [hρ, hL, ← hj, ← this]
      rfl)
    (algebraMap O C cp) hc
    (by
      have := congrArg (fun M => M.map (algebraMap O C)) H.form_eq_alt
      simp only [Matrix.map_sub _ (map_sub (algebraMap O C)), Matrix.map_mul, Matrix.transpose_map] at this
      rw [this]
      ext i k
      simp [f]) τ
  rw [td_base, td_base (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) τ, td_base (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a))]
  exact key
end GlobalTheory.ChF
