-- Prove2me | solution 1 for GlobalTheory.ChF.GenAtPlace.exists_generators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T06:10:45.091683+00:00
-- url     : https://prove2.me/submissions/1b1b1919-87e4-4e46-8c35-01e3c4c68cca

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EmbeddingsLiftIntegersIdempotentsConjugationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EigenbasisRestrictionSurjectiveEquivariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateModuleEigenspaceDimEqLieAlgebraSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PadicPlaceBasisOfIdempotentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFreeGeneratorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PadicIntAlgebraOfIsAdicCompleteMatrixUniqueStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsAbelianTorusGeneratorsAtPlace
import Theorems.Thm_GlobalTheory_ChF_splitEx_one
import Theorems.Thm_GlobalTheory_T_eigenbasis_restriction_surjective_equivariant
import Theorems.Thm_GlobalTheory_T_eigenspaceDim_add_split_exact_transpose
import Theorems.Thm_GlobalTheory_T_embeddings_lift_integers_idempotents_conjugation
import Theorems.Thm_GlobalTheory_T_exists_linearIndependent_spanning_range_mulVec
import Theorems.Thm_GlobalTheory_T_padicInt_algebra_of_isAdicComplete_matrix_unique
import Theorems.Thm_GlobalTheory_T_padic_place_basis_of_idempotent
import Theorems.Thm_GlobalTheory_T_tateModule_eigenspace_dim_eq_lieAlgebra_sum
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_Up_sum_single__5b64b664eaa4
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
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_ne_zero
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
namespace GlobalTheory.ChF.GenAtPlace
private theorem range_map_le {R O κ J : Type} [CommRing R] [CommRing O] [Algebra R O] [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ R) (u : J → κ → R)
    (h : Submodule.span R (Set.range u) = LinearMap.range (Matrix.mulVecLin M)) (x : κ → O) :
    M.map (algebraMap R O) *ᵥ x ∈ Submodule.span O (Set.range fun q => (algebraMap R O) ∘ u q) := by
  have key : ∀ z ∈ Submodule.span R (Set.range u),
      (algebraMap R O) ∘ z ∈ Submodule.span O (Set.range fun q => (algebraMap R O) ∘ u q) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨q, rfl⟩ := hz; exact Submodule.subset_span ⟨q, rfl⟩
    | zero =>
      have : (algebraMap R O) ∘ (0 : κ → R) = 0 := by ext; simp
      rw [this]; exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      have : (algebraMap R O) ∘ (a + b) = (algebraMap R O) ∘ a + (algebraMap R O) ∘ b := by ext; simp
      rw [this]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have : (algebraMap R O) ∘ (c • a) = algebraMap R O c • ((algebraMap R O) ∘ a) := by ext; simp
      rw [this]; exact Submodule.smul_mem _ _ ha
  have : M.map (algebraMap R O) *ᵥ x = ∑ i, x i • ((algebraMap R O) ∘ (M *ᵥ Pi.single i 1)) := by
    ext j
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm, Pi.single_apply]
  rw [this]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (key _ ?_)
  rw [h]; exact ⟨_, rfl⟩
private theorem map_mulVec' {R O κ : Type} [CommRing R] [CommRing O] [Algebra R O] [Fintype κ]
    (M : Matrix κ κ R) (x : κ → R) :
    (algebraMap R O) ∘ (M *ᵥ x) = M.map (algebraMap R O) *ᵥ ((algebraMap R O) ∘ x) := by
  ext j
  simp [Matrix.mulVec, dotProduct]
private theorem quot_onto {O M P Q : Type} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup P]
    [Module O P] [AddCommGroup Q] [Module O Q] (K : M →ₗ[O] P) (S : Submodule O P) (L U : Submodule O Q)
    (β : Q →ₗ[O] M) (h1 : ∀ u ∈ U, K (β u) ∈ S) (h2 : ∀ f, ∃ l ∈ L, K f - K (β l) ∈ S) :
    ∃ f : (L ⧸ U.comap L.subtype) →ₗ[O] (LinearMap.range K ⧸ S.comap (LinearMap.range K).subtype),
      Function.Surjective f := by
  refine ⟨Submodule.mapQ _ _ (K.rangeRestrict.comp (β.comp L.subtype)) ?_, ?_⟩
  · intro x hx
    exact h1 _ hx
  · intro q
    obtain ⟨⟨_, f, rfl⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨l, hl, h⟩ := h2 f
    refine ⟨Submodule.Quotient.mk ⟨l, hl⟩, ?_⟩
    refine (Submodule.mapQ_apply _ _ _ _).trans ((Submodule.Quotient.eq _).2 ?_)
    have := S.neg_mem h
    rw [neg_sub] at this
    exact this
private theorem res_eig {O OE : Type} [CommRing O] [CommRing OE] {d s : ℕ} (ρ : OE → Matrix (Fin d) (Fin d) O)
    (τ : OE →+* O) (W : Fin s → Fin d → O) (h : EigB ρ τ W) (a : OE) (f : Fin d → O) :
    Pdiv.ChartF.res W ((ρ a)ᵀ *ᵥ f) = τ a • Pdiv.ChartF.res W f := by
  ext i
  have h1 : ∀ f, Pdiv.ChartF.res W f i = W i ⬝ᵥ f := fun f => rfl
  rw [Pi.smul_apply, h1, h1, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h.1 i a, smul_dotProduct]
private theorem extM_tmul (p : ℕ) [Fact p.Prime] {O OE κ : Type} [CommRing O] [Algebra ℤ_[p] O] [CommRing OE]
    [Fintype κ] [DecidableEq κ] (ρ : OE →+* Matrix κ κ O) (c : ℤ_[p]) (a : OE) :
    extM p ρ (c ⊗ₜ[ℤ] a) = algebraMap ℤ_[p] O c • ρ a := by
  refine (Algebra.TensorProduct.lift_tmul _ _ _ c a).trans ?_
  show algebraMap ℤ_[p] (Matrix κ κ O) c * ρ a = _
  rw [← Algebra.smul_def, algebraMap_smul]
private theorem eigDim_star (C : Type) [Field C] {O OE κ : Type} [CommRing O] [Algebra O C] [CommRing OE]
    [StarRing OE] [Fintype κ] [DecidableEq κ] (ρ : OE → Matrix κ κ O) (τ : OE →+* C) :
    eigDim C (fun a => ρ (star a)) τ =
      eigDim C ρ (τ.comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) := by
  unfold eigDim
  have : (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' ((ρ (star a)).map (algebraMap O C))) (τ a)) =
      ⨅ a : OE, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C)))
        ((τ.comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) a) := by
    refine (star_involutive.surjective.iInf_congr star fun a => ?_)
    simp
  rw [this]
private theorem wfd (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (w : Place p OE) (b : Module.Basis (Fin w.n) ℤ_[p] w.Ow) (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] Matrix κ κ ℤ_[p]) :
    ∃ (h : ℕ) (y : Fin h → κ → ℤ_[p]),
      Submodule.span ℤ_[p] (Set.range fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) = LinearMap.range (Matrix.mulVecLin (ρ w.e)) ∧
      ∀ τ ∈ Emb (O := O) w.e, eigDim C (fun a : OE => (ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)) ((algebraMap O C).comp τ) = h := by
  obtain ⟨h, y, h1, h2⟩ := GlobalTheory.T.exists_linearIndependent_spanning_range_mulVec p OE ⟨w.e, w.idem, w.ne_zero, w.prim⟩ b κ ρ
  exact ⟨h, y, h2, GlobalTheory.T.padic_place_basis_of_idempotent p C v O hv OE ⟨w.e, w.idem, w.ne_zero, w.prim⟩ b κ ρ h y h1 h2⟩
private theorem mulVec_comb {O I J K : Type} [CommRing O] [Fintype I] [Fintype J] (M : Matrix K J O)
    (c : I → O) (u : I → J → O) : M *ᵥ (∑ i, c i • u i) = ∑ i, c i • (M *ᵥ u i) := by
  show Matrix.mulVecLin M _ = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
private theorem sum_single' {O I : Type} [CommRing O] [Fintype I] [DecidableEq I] (c : I → O) :
    ∑ i, c i • (Pi.single i 1 : I → O) = c := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]
private theorem mulVec_cols {O I K : Type} [CommRing O] [Fintype I] (M : Matrix K I O) (c : I → O) :
    M *ᵥ c = ∑ i, c i • (fun l => M l i) := by
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
private theorem core {R O Λ I J Y : Type} [CommRing R] [CommRing O] [Algebra R O] [Fintype I] [DecidableEq I]
    {d r g h₁ h₂ : ℕ} (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (hex : SplitEx A B)
    (G : Λ → Matrix (Fin d) (Fin d) O) (L : Λ → Matrix (Fin g) (Fin g) O) (Nt : Λ → Matrix (Fin r) (Fin r) R)
    (ρ : Λ → Matrix I I R) (Ht : Matrix (Fin g) I O) (hB : ∀ x, B * G x = L x * B)
    (hA : ∀ x, Aᵀ * (G x)ᵀ = (Nt x).map (algebraMap R O) * Aᵀ)
    (hH : ∀ x, Ht * (ρ x).map (algebraMap R O) = (L x)ᵀ * Ht)
    (K : (Fin d → O) →ₗ[O] (Y → O)) (T : Λ → Y → O) (hK : ∀ x f, K ((G x)ᵀ *ᵥ f) = T x * K f)
    (e : Λ) (he : T e = 1) (b : J → Λ) (y : Fin h₁ → I → R) (z : Fin h₂ → Fin r → R)
    (hy : Submodule.span R (Set.range fun q : J × Fin h₁ => ρ (b q.1) *ᵥ y q.2) =
      LinearMap.range (Matrix.mulVecLin (ρ e)))
    (hz : Submodule.span R (Set.range fun q : J × Fin h₂ => Nt (b q.1) *ᵥ z q.2) =
      LinearMap.range (Matrix.mulVecLin (Nt e)))
    (φ : Fin h₂ → Fin d → O) (hφ : ∀ l, Aᵀ *ᵥ φ l = algebraMap R O ∘ z l)
    (S : Submodule O (Y → O))
    (hS₁ : ∀ k l, T (b k) * K (Bᵀ *ᵥ (Ht *ᵥ (algebraMap R O ∘ y l))) ∈ S)
    (hS₂ : ∀ k l, T (b k) * K (φ l) ∈ S) :
    (∀ u ∈ (LinearMap.range (Matrix.mulVecLin ((ρ e).map (algebraMap R O)))).map (Matrix.mulVecLin Ht),
      K (Matrix.mulVecLin Bᵀ u) ∈ S) ∧
    ∀ f, ∃ l ∈ LinearMap.range (Matrix.mulVecLin (L e)ᵀ), K f - K (Matrix.mulVecLin Bᵀ l) ∈ S := by
  have hBt : ∀ x l, Bᵀ *ᵥ ((L x)ᵀ *ᵥ l) = (G x)ᵀ *ᵥ (Bᵀ *ᵥ l) := by
    intro x l
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hB]
  constructor
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    have h := range_map_le (O := O) _ _ hy x
    have hle : Submodule.span O (Set.range fun q : J × Fin h₁ => algebraMap R O ∘ (ρ (b q.1) *ᵥ y q.2)) ≤
        S.comap (K.comp ((Matrix.mulVecLin Bᵀ).comp (Matrix.mulVecLin Ht))) := by
      rw [Submodule.span_le]
      rintro _ ⟨q, rfl⟩
      show K (Bᵀ *ᵥ (Ht *ᵥ (algebraMap R O ∘ (ρ (b q.1) *ᵥ y q.2)))) ∈ S
      rw [map_mulVec', Matrix.mulVec_mulVec _ Ht, hH, ← Matrix.mulVec_mulVec, hBt, hK]
      exact hS₁ _ _
    exact hle h
  · intro f
    have h := range_map_le (O := O) _ _ hz (Aᵀ *ᵥ f)
    have hle : Submodule.span O (Set.range fun q : J × Fin h₂ => algebraMap R O ∘ (Nt (b q.1) *ᵥ z q.2)) ≤
        (S.comap K).map (Matrix.mulVecLin Aᵀ) := by
      rw [Submodule.span_le]
      rintro _ ⟨q, rfl⟩
      refine ⟨(G (b q.1))ᵀ *ᵥ φ q.2, ?_, ?_⟩
      · show K _ ∈ S
        rw [hK]; exact hS₂ _ _
      · show Aᵀ *ᵥ _ = algebraMap R O ∘ (Nt (b q.1) *ᵥ z q.2)
        rw [map_mulVec', ← hφ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA]
    obtain ⟨u, hu, hAu⟩ := hle h
    have hAu' : Aᵀ *ᵥ ((G e)ᵀ *ᵥ f - u) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hA, ← Matrix.mulVec_mulVec, ← hAu]
      exact sub_self _
    obtain ⟨-, A', B', -, -, h3⟩ := hex
    have h4 : Bᵀ *ᵥ (B'ᵀ *ᵥ ((G e)ᵀ *ᵥ f - u)) = (G e)ᵀ *ᵥ f - u := by
      have h5 : A'ᵀ * Aᵀ + Bᵀ * B'ᵀ = 1 := by
        rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.transpose_add, h3, Matrix.transpose_one]
      conv_rhs => rw [← Matrix.one_mulVec ((G e)ᵀ *ᵥ f - u), ← h5]
      rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAu', Matrix.mulVec_zero, zero_add]
    refine ⟨(L e)ᵀ *ᵥ (B'ᵀ *ᵥ ((G e)ᵀ *ᵥ f - u)), ⟨_, rfl⟩, ?_⟩
    show K f - K (Bᵀ *ᵥ _) ∈ S
    rw [hBt, h4, hK, map_sub, hK, he, _root_.one_mul, _root_.one_mul, sub_sub_cancel]
    exact hu
end GlobalTheory.ChF.GenAtPlace
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF GlobalTheory.ChF.GenAtPlace
namespace GlobalTheory.ChF.GenAtPlace
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (α : ℤ_[p] ⊗[ℤ] OE) (b : Module.Basis (Fin w.n) ℤ_[p] w.Ow), (∀ k, (b k : ℤ_[p] ⊗[ℤ] OE) = w.e * α ^ (k : ℕ)) → ∀ (rp rm : ℕ) (W : Fin w.n → Fin rp → Fin d → O), (∀ j, EigB ρG ((t j : Emb (O := O) w.e) : OE →+* O) (W j)) → (∀ τ ∈ Emb (O := O) w.bar, eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp τ) ≤ rm) → ∃ (h : ℕ) (ψ : Fin h → Fin d → O), h ≤ rp + rm ∧ (∀ l j, Pdiv.ChartF.res (W j) (ψ l) ∈ Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W j) (s k))) ∧ ∃ f : htCoker H w.e w.bar →ₗ[O] ((LinearMap.range (LinearMap.pi fun y : Fin w.n × Fin rp => (LinearMap.proj y.2).comp (Pdiv.ChartF.res (W y.1))) : Submodule O (Fin w.n × Fin rp → O)) ⧸ (Submodule.span O (Set.range fun q : Fin w.n × Fin h => fun y : Fin w.n × Fin rp => tauExt ((t y.1 : Emb (O := O) w.e) : OE →+* O) α ^ (q.1 : ℕ) * Pdiv.ChartF.res (W y.1) (ψ q.2) y.2)).comap (Submodule.subtype _)), Function.Surjective f := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hU g H d r m A B ρG N s hL w t α b hb rp rm W hW hrm
  classical
  obtain ⟨-, -, hstar⟩ := GlobalTheory.T.embeddings_lift_integers_idempotents_conjugation p C v O hv OE
  have hzp := (GlobalTheory.T.padicInt_algebra_of_isAdicComplete_matrix_unique p O).2
  have hbar : ∀ τ : OE →+* O, w.bar = sigE p OE w.e := fun τ => (hstar τ w.e).2

  let NZ : OE →+* Matrix (Fin r) (Fin r) ℤ_[p] := ((Int.castRingHom ℤ_[p]).mapMatrix).comp N
  let NO : OE →+* Matrix (Fin r) (Fin r) O := ((Int.castRingHom O).mapMatrix).comp N
  let LB : OE →+* Matrix (Fin g) (Fin g) O :=
    H.ρL.comp (Algebra.TensorProduct.includeRight : OE →ₐ[ℤ] ℤ_[p] ⊗[ℤ] OE).toRingHom
  have hLB : ∀ a, LB a = H.ρL (1 ⊗ₜ[ℤ] a) := fun a => rfl
  have hNO : ∀ a, ((NZ a)ᵀ).map (algebraMap ℤ_[p] O) = (NO a)ᵀ := by
    intro a; ext i j; simp [NZ, NO]
  have hLt : ∀ (c : ℤ_[p]) (a : OE), H.ρL (c ⊗ₜ[ℤ] a) = algebraMap ℤ_[p] O c • H.ρL (1 ⊗ₜ[ℤ] a) := by
    intro c a
    have h1 : (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = algebraMap ℤ_[p] _ c * (1 ⊗ₜ[ℤ] a) := by
      simp [Algebra.TensorProduct.algebraMap_apply]
    have h2 := hzp g (H.ρL.comp (algebraMap ℤ_[p] _)) c
    rw [RingHom.comp_apply] at h2
    rw [h1, map_mul, h2, smul_mul_assoc, _root_.one_mul]
  have hB : ∀ x, B * extM p ρG x = H.ρL x * B := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c a => rw [extM_tmul, hLt, Matrix.mul_smul, Matrix.smul_mul, hL.eqB]
    | add x x' h h' => rw [map_add, map_add, Matrix.mul_add, Matrix.add_mul, h, h']
  have hA : ∀ x, Aᵀ * (extM p ρG x)ᵀ = (extM p (trR NZ) x).map (algebraMap ℤ_[p] O) * Aᵀ := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c a =>
      have h1 : (algebraMap ℤ_[p] ℤ_[p] c • trR NZ a).map (algebraMap ℤ_[p] O) =
          algebraMap ℤ_[p] O c • (NO a)ᵀ := by
        rw [← hNO]; ext i j; simp [trR]
      rw [extM_tmul, extM_tmul, h1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul,
        ← Matrix.transpose_mul, ← Matrix.transpose_mul, hL.eqA]
      rfl
    | add x x' h h' =>
      rw [map_add, map_add, Matrix.transpose_add, Matrix.mul_add, h, h', Matrix.map_add _ (map_add _),
        Matrix.add_mul]
  let ρ' : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] Matrix (Ix g) (Ix g) ℤ_[p] := H.ρ.comp (sigE p OE).toAlgHom
  have hρ' : ∀ x, ρ' x = H.ρ (sigE p OE x) := fun x => rfl
  have hH : ∀ x, H.Ht * (ρ' x).map (algebraMap ℤ_[p] O) = (H.ρL x)ᵀ * H.Ht := by
    intro x
    rw [hρ', H.Ht_equivariant.1, hU.invol]
  have hres : ∀ j x f, Pdiv.ChartF.res (W j) ((extM p ρG x)ᵀ *ᵥ f) =
      tauExt ((t j : Emb (O := O) w.e) : OE →+* O) x • Pdiv.ChartF.res (W j) f := by
    intro j x f
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c a =>
      rw [extM_tmul, Matrix.transpose_smul, Matrix.smul_mulVec, map_smul, res_eig _ _ _ (hW j), smul_smul]
      congr 1
    | add x x' h h' => rw [map_add, map_add, Matrix.transpose_add, Matrix.add_mulVec, map_add, h, h', add_smul]
  obtain ⟨h₁, y, hy, hyd⟩ := wfd p C v O hv OE w b (Ix g) ρ'
  obtain ⟨h₂, z, hz, hzd⟩ := wfd p C v O hv OE w b (Fin r) (extM p (trR NZ))
  choose kB hkB using hL.fromB
  choose kT hkT using hL.fromT
  let φ : Fin h₂ → Fin d → O := fun l => ∑ i, algebraMap ℤ_[p] O (z l i) • s (kT i)
  have hφ : ∀ l, Aᵀ *ᵥ φ l = algebraMap ℤ_[p] O ∘ z l := by
    intro l
    show Aᵀ *ᵥ (∑ i, algebraMap ℤ_[p] O (z l i) • s (kT i)) = _
    rw [mulVec_comb]
    simp only [hkT]
    exact sum_single' _
  let χ : Fin h₁ → Fin d → O := fun l => Bᵀ *ᵥ (H.Ht *ᵥ (algebraMap ℤ_[p] O ∘ y l))
  have hχ : ∀ l, χ l = ∑ i, algebraMap ℤ_[p] O (y l i) • s (kB i) := by
    intro l
    show Bᵀ *ᵥ (H.Ht *ᵥ (algebraMap ℤ_[p] O ∘ y l)) = _
    rw [mulVec_cols H.Ht, mulVec_comb]
    simp only [hkB]
    rfl

  have hn : Nonempty (Fin w.n) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have hs : Subsingleton w.Ow := b.repr.toEquiv.subsingleton
    have h1 : (⟨w.e, ⟨1, by simp⟩⟩ : w.Ow) = 0 := Subsingleton.elim _ _
    exact w.ne_zero (congrArg Subtype.val h1)
  obtain ⟨j₀⟩ := hn
  refine ⟨h₁ + h₂, Fin.append χ φ, ?_, ?_, ?_⟩
  · set τ : OE →+* O := ((t j₀ : Emb (O := O) w.e) : OE →+* O) with hτ
    have hτe : τ ∈ Emb (O := O) w.e := (t j₀).2
    have e1 := hyd τ hτe
    have e2 := hzd τ hτe
    have e3 := (GlobalTheory.T.eigenbasis_restriction_surjective_equivariant C v O hv OE d rp ρG τ (W j₀) (hW j₀)).2.2
    have e4 := (GlobalTheory.T.eigenspaceDim_add_split_exact_transpose C O OE d r g A B hL.exact ρG NO LB hL.eqB hL.eqA ((algebraMap O C).comp τ)).1
    have e5 := (GlobalTheory.T.eigenspaceDim_add_split_exact_transpose C O OE r r 0 1 0 (splitEx_one r) NO NO
      ⟨⟨⟨fun _ => 1, rfl⟩, fun _ _ => Subsingleton.elim _ _⟩, Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
      (fun a => Subsingleton.elim _ _) (fun a => by simp) ((algebraMap O C).comp τ)).2
    have e2' : (fun a : OE => (extM p (trR NZ) (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)) = fun a => (NO a)ᵀ := by
      funext a
      rw [extM_tmul, map_one, one_smul]; exact hNO a
    rw [e2', e5] at e2
    have e1' : (fun a : OE => (ρ' (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)) =
        fun a => (fun a : OE => (H.ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)) (star a) := by
      funext a
      rfl
    rw [e1', eigDim_star C (fun a : OE => (H.ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)), GlobalTheory.T.tateModule_eigenspace_dim_eq_lieAlgebra_sum p C v O hv OE cp hU g H] at e1
    have e6 : (((algebraMap O C).comp τ).comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom).comp
        ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom = (algebraMap O C).comp τ := by
      ext a; simp
    rw [e6] at e1
    have e7 := hrm (τ.comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) (by
      show tauExt _ _ = 1
      rw [(hstar τ _).1, hbar τ, hU.invol]; exact hτe)
    rw [← RingHom.comp_assoc] at e7
    have e8 : eigDim C LB ((algebraMap O C).comp τ) =
      eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp τ) := rfl
    omega
  · intro l j
    refine Fin.addCases (fun l => ?_) (fun l => ?_) l
    · rw [Fin.append_left, hχ, map_sum]
      exact Submodule.sum_mem _ fun i _ => by
        rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · rw [Fin.append_right, map_sum]
      exact Submodule.sum_mem _ fun i _ => by
        rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · have hTb : ∀ j k, tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b k : ℤ_[p] ⊗[ℤ] OE) =
        tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α ^ (k : ℕ) := by
      intro j k
      have : tauExt ((t j : Emb (O := O) w.e) : OE →+* O) w.e = 1 := (t j).2
      rw [hb, map_mul, map_pow, this, _root_.one_mul]
    obtain ⟨c1, c2⟩ := core A B hL.exact (extM p ρG) H.ρL (extM p (trR NZ)) ρ' H.Ht hB hA hH
      (LinearMap.pi fun y : Fin w.n × Fin rp => (LinearMap.proj y.2).comp (Pdiv.ChartF.res (W y.1)))
      (fun x y => tauExt ((t y.1 : Emb (O := O) w.e) : OE →+* O) x)
      (fun x f => by
        ext y
        show Pdiv.ChartF.res (W y.1) _ y.2 = _
        rw [hres]; rfl)
      w.e (by ext y; exact (t y.1).2) (fun k => (b k : ℤ_[p] ⊗[ℤ] OE)) y z hy hz φ hφ
      (Submodule.span O (Set.range fun q : Fin w.n × Fin (h₁ + h₂) => fun y : Fin w.n × Fin rp =>
        tauExt ((t y.1 : Emb (O := O) w.e) : OE →+* O) α ^ (q.1 : ℕ) *
          Pdiv.ChartF.res (W y.1) (Fin.append χ φ q.2) y.2))
      (fun k l => Submodule.subset_span ⟨(k, Fin.castAdd h₂ l), by
        ext y
        simp only [Fin.append_left, Pi.mul_apply, hTb]
        rfl⟩)
      (fun k l => Submodule.subset_span ⟨(k, Fin.natAdd h₁ l), by
        ext y
        simp only [Fin.append_right, Pi.mul_apply, hTb]
        rfl⟩)
    refine quot_onto _ _ (lieDPart H w.e) _ (Matrix.mulVecLin Bᵀ) ?_ c2
    rw [hbar (t j₀ : Emb (O := O) w.e)]
    exact c1
end GlobalTheory.ChF.GenAtPlace
