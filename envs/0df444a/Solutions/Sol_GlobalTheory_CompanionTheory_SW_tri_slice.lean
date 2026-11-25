-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.tri_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:16:53.329501+00:00
-- url     : https://prove2.me/submissions/c9a60d9d-f39b-42d5-9b0f-8c67cc8a038d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOpenChartDiagonalUnipotentStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHermitianDiagonalizationUnitsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentitiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOrbitLocalSectionSubgroup
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Tri_aMat_gram
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Tri_sq_open
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Tri_conj_case
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_half_trace_tmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_zero
import Theorems.Thm_GlobalTheory_T_gram_right_action_identities
import Theorems.Thm_GlobalTheory_T_hermitian_open_chart_diagonal_unipotent
import Theorems.Thm_GlobalTheory_T_local_hermitian_diagonalization_units
import Theorems.Thm_GlobalTheory_T_tensor_locally_compact_ring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_zero



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW
open GlobalTheory.CompanionTheory.SW.Tri
namespace GlobalTheory.CompanionTheory.SW
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (S : HermR R σ n), IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ (Q : Subgroup (GL (Fin n) (R ⊗[F] E))) (o : Q → HermR R σ n), LocallyCompactSpace Q ∧ SecondCountableTopology Q ∧ IsOpenEmbedding o ∧ ∀ x : Q, (o x : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) ((x : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * ((x : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ hR n S hS
  have hR' := hR
  obtain ⟨i1, i2, i3, i4, i5, i6, hval, U, -, hU⟩ := hR'
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  haveI := i5
  haveI := i6
  obtain ⟨k1, k2, k3, k4, -, htr, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := k1
  haveI := k2
  haveI := k3
  haveI := k4
  obtain ⟨o, ho, hof⟩ := GlobalTheory.T.hermitian_open_chart_diagonal_unipotent F E σ hCM R hR n
  obtain ⟨g, d, hg, hSg⟩ := GlobalTheory.T.local_hermitian_diagonalization_units F E σ hCM R n S hS
  have hH : ∀ S' ∈ HermR R σ n, ∀ g' : Matrix (Fin n) (Fin n) (R ⊗[F] E),
      cT (sigR R σ) g' * S' * g' ∈ HermR R σ n := fun S' hS' g' =>
    (GlobalTheory.T.gram_right_action_identities F E σ hCM 0 0 ⟨fun i => i.elim0, by simp⟩ R n).2.2.2.1 ⟨S', hS'⟩ g'
  let ι : R →+* R ⊗[F] E := Algebra.TensorProduct.includeLeftRingHom
  have hιa : ∀ r, ι r = r ⊗ₜ[F] (1 : E) := fun r => rfl
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
  have hι : Continuous ι := by
    have : (ι : R → R ⊗[F] E) = fun r => r • (1 : R ⊗[F] E) := by
      funext r
      rw [hιa, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact (continuous_id : Continuous fun r : R => r).smul (continuous_const : Continuous fun _ : R => (1 : R ⊗[F] E))
  let π : R ⊗[F] E → R := fun k => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) k
  have hπ : Continuous π := continuous_const.mul htr
  have hπι : ∀ r, π (ι r) = r := fun r => half_trace_tmul hCM.2.2.1 R r
  have hs : ∀ r, sigR R σ (ι r) = ι r := fun r => by simp [hιa, sigR]
  let Ψ := triHomeo (n := n) ι hι π hπ hπι hval.isInducing U
  have hP := sq_open (K := R ⊗[F] E) U hU d
  let Φ : triSub ι U n → (Fin n → Rˣ) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
    fun x => (fun i => (uOf ι x i : Rˣ) ^ 2 * d i, mOf ι x)
  have hΦ : IsOpenEmbedding Φ := hP.comp Ψ.symm.isOpenEmbedding
  haveI : LocallyCompactSpace Rˣ := hval.locallyCompactSpace
  haveI : SecondCountableTopology Rˣ := hval.isEmbedding.secondCountableTopology
  have lc₀ : LocallyCompactSpace (triSub ι U n) := hΦ.locallyCompactSpace
  have sc₀ : SecondCountableTopology (triSub ι U n) := hΦ.isEmbedding.secondCountableTopology
  let D : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
    Matrix.diagonal (fun i => ((d i : R) ⊗ₜ[F] (1 : E) : R ⊗[F] E))
  have hf : ∀ x : triSub ι U n, (o (Φ x) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      cT (sigR R σ) ((x : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * D *
        ((x : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
    intro x
    have hxa : ((x : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
        = aMat ι (uOf ι x) (mOf ι x) := by
      conv_lhs => rw [← aGL_coords ι x]
      rfl
    rw [hxa]
    have := aMat_gram ι (sigR R σ) hs (uOf ι x) (mOf ι x) d
    exact (hof _ _ (nMat (mOf ι x)) rfl).trans this.symm
  have hgu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 hg
  obtain ⟨Q, e, o', ho', hform⟩ := conj_case (sigR R σ) (HermR R σ n) hH hgu.unit (triSub ι U n)
    (fun x => o (Φ x)) (ho.comp hΦ) D hf
  refine ⟨Q, o', e.isOpenEmbedding.locallyCompactSpace, e.isEmbedding.secondCountableTopology, ho', ?_⟩
  intro x
  rw [hform x, hSg]
  rfl
end GlobalTheory.CompanionTheory.SW
