-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramNear.exists_fibre_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:01:15.566447+00:00
-- url     : https://prove2.me/submissions/eacd0a47-362b-48c6-b9dc-001fca390c6f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentitiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOrbitLocalSectionSubgroupStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityFormulaStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarModularCharacterOfContinuousActionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureDisintegrationFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramNear_fibre_on_orbit
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_zero
import Theorems.Thm_GlobalTheory_T_gram_right_action_identities
import Theorems.Thm_GlobalTheory_T_hermitian_matrices_locally_compact_borel
import Theorems.Thm_GlobalTheory_T_hermitian_orbit_local_section_subgroup
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramNear
namespace GlobalTheory.CompanionTheory.SW.GramNear
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ S : HermR R σ n, IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ B : Set (HermR R σ n), IsOpen B ∧ S ∈ B ∧ (∀ S' ∈ B, IsUnit (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ∧ ∃ fib, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (gramR R σ J ⁻¹' (Subtype.val '' B)) ν B fib := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν hμ hν S hS
  have hR' := hR
  obtain ⟨_, _, _, _, -, -, -, -⟩ := hR'
  obtain ⟨_, _, _, _, hsig, -, -, hbor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  have hbor' := hbor n M
  obtain ⟨_, _, _, _, hlift⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R n
  obtain ⟨g, hgc, hgf⟩ := hlift M J hJ
  obtain ⟨hgram, hmul, hone, hherm, -⟩ := GlobalTheory.T.gram_right_action_identities F E σ hσ M J hJ R n
  obtain ⟨Q, o, _, _, hoe, ho⟩ := GlobalTheory.T.hermitian_orbit_local_section_subgroup F E σ hσ R hR n S hS

  let c : Q → Matrix (Fin n) (Fin n) (R ⊗[F] E) := fun q => (((q⁻¹ : Q) : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
  have hc1 : c 1 = 1 := by simp [c]
  have hcm : ∀ a b : Q, c (a * b) = c b * c a := by
    intro a b
    simp only [c, mul_inv_rev]
    rfl
  have hcc : Continuous c := Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)
  letI actV : DistribMulAction Q (Fin n → Fin M → R ⊗[F] E) :=
    { smul := fun q X => rmul R X (c q)
      one_smul := fun X => by
        change rmul R X (c 1) = X
        rw [hc1, hone]
      mul_smul := fun a b X => by
        change rmul R X (c (a * b)) = rmul R (rmul R X (c b)) (c a)
        rw [hcm, hmul]
      smul_zero := fun q => by
        change rmul R 0 (c q) = 0
        funext a i; simp [rmul]
      smul_add := fun q X Y => by
        change rmul R (X + Y) (c q) = rmul R X (c q) + rmul R Y (c q)
        funext a i; simp [rmul, add_mul, Finset.sum_add_distrib] }
  have hsmulV : ∀ (q : Q) (X : Fin n → Fin M → R ⊗[F] E), q • X = rmul R X (c q) := fun _ _ => rfl
  letI actH : DistribMulAction Q (HermR R σ n) :=
    { smul := fun q T => ⟨cT (sigR R σ) (c q) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q, hherm T (c q)⟩
      one_smul := fun T => by
        apply Subtype.ext
        change cT (sigR R σ) (c 1) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c 1 = T
        rw [hc1]; simp [cT]
      mul_smul := fun a b T => by
        apply Subtype.ext
        change cT (sigR R σ) (c (a * b)) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c (a * b) =
          cT (sigR R σ) (c a) * (cT (sigR R σ) (c b) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c b) * c a
        rw [hcm]
        simp only [cT, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      smul_zero := fun q => by
        apply Subtype.ext
        change cT (sigR R σ) (c q) * (0 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q = 0
        simp
      smul_add := fun q T T' => by
        apply Subtype.ext
        change cT (sigR R σ) (c q) * ((T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) + T') * c q =
          cT (sigR R σ) (c q) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q +
            cT (sigR R σ) (c q) * (T' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q
        rw [Matrix.mul_add, Matrix.add_mul] }
  have hsmulH : ∀ (q : Q) (T : HermR R σ n), ((q • T : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      cT (sigR R σ) (c q) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q := fun _ _ => rfl
  have hcontV : ContinuousSMul Q (Fin n → Fin M → R ⊗[F] E) := by
    refine ⟨?_⟩
    change Continuous fun p : Q × (Fin n → Fin M → R ⊗[F] E) => rmul R p.2 (c p.1)
    refine continuous_pi fun a => continuous_pi fun i => ?_
    simp only [rmul]
    refine continuous_finset_sum _ fun b _ => Continuous.mul ?_ ?_
    · exact (continuous_apply i).comp ((continuous_apply b).comp continuous_snd)
    · exact (hcc.comp continuous_fst).matrix_elem b a
  have hcontH : ContinuousSMul Q (HermR R σ n) := by
    refine ⟨?_⟩
    refine Continuous.subtype_mk (f := fun p : Q × HermR R σ n => cT (sigR R σ) (c p.1) * (p.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c p.1) ?_ _
    have h1 : Continuous fun p : Q × HermR R σ n => c p.1 := hcc.comp continuous_fst
    have h2 : Continuous fun p : Q × HermR R σ n => cT (sigR R σ) (c p.1) :=
      (h1.matrix_map hsig).matrix_transpose
    exact (h2.matrix_mul (continuous_subtype_val.comp continuous_snd)).matrix_mul h1
  have heq : ∀ (q : Q) (X : Fin n → Fin M → R ⊗[F] E), g (q • X) = q • g X := by
    intro q X
    apply Subtype.ext
    rw [hsmulV, hsmulH, ← hgf, ← hgf, hgram]
  have horb : IsOpenEmbedding (fun q : Q => q • S) := by
    have : (fun q : Q => q • S) = o ∘ (Homeomorph.inv Q) := by
      funext q
      apply Subtype.ext
      rw [hsmulH]
      exact (ho q⁻¹).symm
    rw [this]
    exact hoe.comp (Homeomorph.inv Q).isOpenEmbedding
  obtain ⟨fib, hfib⟩ := fibre_on_orbit (Fin n → Fin M → R ⊗[F] E) (HermR R σ n) (Matrix (Fin n) (Fin n) (R ⊗[F] E))
    μ ν (gramR R σ J) g Subtype.val Subtype.val_injective hgc hgf Q heq S horb
  refine ⟨Set.range fun q : Q => q • S, horb.isOpen_range, ⟨1, one_smul _ _⟩, ?_, fib, ?_⟩
  · rintro _ ⟨q, rfl⟩
    change IsUnit ((q • S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det
    rw [hsmulH]
    have hdc : IsUnit (c q).det := Matrix.isUnits_det_units _
    have hdc' : IsUnit (cT (sigR R σ) (c q)).det := by
      simp only [cT, Matrix.det_transpose]
      have := hdc.map (sigR R σ)
      rwa [RingHom.map_det] at this
    rw [Matrix.det_mul, Matrix.det_mul]
    exact (hdc'.mul hS).mul hdc
  · have hpre : gramR R σ J ⁻¹' (Subtype.val '' (Set.range fun q : Q => q • S)) = g ⁻¹' (Set.range fun q : Q => q • S) := by
      ext X
      simp only [Set.mem_preimage, hgf X]
      exact Subtype.val_injective.mem_set_image
    rw [hpre]
    exact hfib
end GlobalTheory.CompanionTheory.SW.GramNear
