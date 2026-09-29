-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_iotaGL_invariant_rsLocalIntegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/bfb2f92d-5b4b-5952-a090-50bc861ece53

import Mathlib
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_HaarQuotient
import Theorems.Thm_RSCarrier_rsLocalIntegral_comp_mul_right_eq_mul_rsLocalIntegral_of_map_mul_right_eq
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_of_isHaarMeasure_fin_two
import Theorems.Thm_AdelicDock_isCompact_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_invariant_rsLocalIntegral_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

open LanglandsTunnell.CubicInduction
open scoped ENNReal NNReal Matrix

noncomputable section

namespace KAvg

section Kit

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem coe_modulus_eq_norm (x : F) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion ℚ p))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountableTopology_localGL : SecondCountableTopology G :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

scoped instance locallyCompactSpace_localGL' : LocallyCompactSpace G := locallyCompactSpace_localGL ℚ p

abbrev unip : Subgroup G := (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range

theorem continuous_entry (i j : Fin 2) : Continuous fun g : G => (g : Mat) i j :=
  (Units.continuous_val).matrix_elem i j

theorem coe_unip_eq :
    ((unip p : Subgroup G) : Set G) = {g : G | (g : Mat) 0 0 = 1 ∧ (g : Mat) 1 0 = 0 ∧ (g : Mat) 1 1 = 1} := by
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    simp [unipotentGL2Hom, unipotentGL2_coe]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Mat) 0 1), Units.ext ?_⟩
    change ((unipotentGL2 ((g : Mat) 0 1) : G) : Mat) = (g : Mat)
    rw [unipotentGL2_coe]
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

theorem isClosed_unip : IsClosed ((unip p : Subgroup G) : Set G) := by
  rw [coe_unip_eq]
  exact ((isClosed_singleton.preimage (continuous_entry p 0 0)).inter
    ((isClosed_singleton.preimage (continuous_entry p 1 0)).inter
      (isClosed_singleton.preimage (continuous_entry p 1 1))))

theorem unip_eq_unipotentGL2 (n : unip p) : (n : G) = unipotentGL2 (((n : G) : Mat) 0 1) := by
  obtain ⟨z, hz⟩ := n.2
  rw [← hz]
  change (unipotentGL2 z.toAdd : G) = unipotentGL2 (((unipotentGL2 z.toAdd : G) : Mat) 0 1)
  have h01 : (((unipotentGL2 z.toAdd : G) : Mat) 0 1) = z.toAdd := by simp [unipotentGL2_coe]
  rw [h01]

theorem unip_comm (m n : unip p) : m * n = n * m := by
  refine Subtype.ext ?_
  change (m : G) * (n : G) = (n : G) * (m : G)
  rw [unip_eq_unipotentGL2 p m, unip_eq_unipotentGL2 p n, ← unipotentGL2_add, ← unipotentGL2_add, add_comm]

theorem det_unipotentGL2 (x : F) : Matrix.GeneralLinearGroup.det (unipotentGL2 x : G) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

scoped instance locallyCompactSpace_unip : LocallyCompactSpace (unip p) := (isClosed_unip p).locallyCompactSpace

scoped instance secondCountable_unip : SecondCountableTopology (unip p) :=
  TopologicalSpace.Subtype.secondCountableTopology ((unip p : Subgroup G) : Set G)

theorem isMulRightInvariant_unip [MeasurableSpace G] [BorelSpace G] (μN : Measure (unip p)) [μN.IsMulLeftInvariant] :
    μN.IsMulRightInvariant := by
  refine ⟨fun n₀ => ?_⟩
  have h : (fun n : unip p => n * n₀) = fun n => n₀ * n := funext fun n => unip_comm p n n₀
  rw [h]
  exact map_mul_left_eq_self μN n₀

theorem continuous_iotaGL : Continuous fun g : G => (iotaGL g : G₃) := by
  rw [Units.continuous_iff]
  have hc : ∀ i j : Fin 2, Continuous fun g : G => (g : Mat) i j := continuous_entry p
  have hci : ∀ i j : Fin 2, Continuous fun g : G => ((g⁻¹ : G) : Mat) i j := fun i j =>
    (Units.continuous_coe_inv).matrix_elem i j
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp only [Function.comp_apply, coe_iotaGL, embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
        Matrix.cons_val_fin_one] <;>
      first | exact continuous_const | exact hc _ _
  · have h : ∀ g : G, ((((iotaGL g : G₃)⁻¹ : G₃)) : Matrix (Fin 3) (Fin 3) F) = embedMat2 ((g⁻¹ : G) : Mat) :=
      fun g => by rw [← map_inv, coe_iotaGL]
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp only [embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first | exact continuous_const | exact hci _ _

theorem continuous_of_rightInvariant {H : Type*} [Group H] [TopologicalSpace H] [ContinuousMul H]
    {α : Type*} [TopologicalSpace α]
    {f : H → α} {U : Subgroup H} (hU : IsOpen (U : Set H)) (hf : ∀ k ∈ U, ∀ g : H, f (g * k) = f g) :
    Continuous f := by
  refine (IsLocallyConstant.iff_exists_open f).mpr (fun x => ?_) |>.continuous
  refine ⟨(fun h => x⁻¹ * h) ⁻¹' (U : Set H), hU.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro y hy
    have := hf (x⁻¹ * y) hy x
    rwa [mul_inv_cancel_left] at this

theorem continuous_modulus_det :
    Continuous fun g : G =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ) : ℂ) := by
  have : (fun g : G => ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) :
      ℝ) : ℂ)) = fun g : G => ((‖(g : Mat).det‖ : ℝ) : ℂ) := by
    funext g
    rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
  rw [this]
  exact Complex.continuous_ofReal.comp (continuous_norm.comp (Units.continuous_val.matrix_det))

end Kit

section TI

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

theorem continuous_transposeInv3 : Continuous (transposeInv3 : GL (Fin 3) A → GL (Fin 3) A) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun g : GL (Fin 3) A => (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ
    exact Units.continuous_coe_inv.matrix_transpose
  · show Continuous fun g : GL (Fin 3) A => (((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ
    exact Units.continuous_val.matrix_transpose

end TI

section K2

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

abbrev K2 : Subgroup G := AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤

theorem mem_K2_iff (k : G) :
    k ∈ K2 p ↔ (∀ i j, (k : Mat) i j ∈ p.adicCompletionIntegers ℚ) ∧
      ∀ i j, ((k⁻¹ : G) : Mat) i j ∈ p.adicCompletionIntegers ℚ := by
  rw [K2, AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩
    have e : AdelicLevel.idealBound (𝓞 ℚ) (⊤ : Ideal (𝓞 ℚ)) p = 1 := AdelicLevel.idealBound_top p
    refine ⟨⟨h1, ?_, ?_⟩, ⟨h2, ?_, ?_⟩⟩
    · rw [e]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h1 1 0)
    · rw [e]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (sub_mem (h1 1 1) (one_mem _))
    · rw [e]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h2 1 0)
    · rw [e]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (sub_mem (h2 1 1) (one_mem _))

theorem isOpen_integers : IsOpen (p.adicCompletionIntegers ℚ : Set F) :=
  (AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 ℚ) ℚ).out p

theorem isOpen_K2 : IsOpen ((K2 p : Subgroup G) : Set G) := by
  have : ((K2 p : Subgroup G) : Set G) = (⋂ i, ⋂ j, (fun k : G => (k : Mat) i j) ⁻¹' (p.adicCompletionIntegers ℚ : Set F)) ∩
      ⋂ i, ⋂ j, (fun k : G => ((k⁻¹ : G) : Mat) i j) ⁻¹' (p.adicCompletionIntegers ℚ : Set F) := by
    ext k
    simp only [SetLike.mem_coe, mem_K2_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  refine (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_integers p).preimage (continuous_entry p i j)).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_integers p).preimage ((Units.continuous_coe_inv).matrix_elem i j))

theorem isCompact_K2 : IsCompact ((K2 p : Subgroup G) : Set G) :=
  AdelicDock.isCompact_localLevelOne (𝓞 ℚ) ℚ p ⊤

theorem modulus_det_eq_one {k : G} (hk : k ∈ K2 p) :
    ((modulus ((Matrix.GeneralLinearGroup.det k : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ)) = 1 := by
  rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
  obtain ⟨h1, h2⟩ := (mem_K2_iff p k).1 hk

  have hd : (k : Mat).det ∈ p.adicCompletionIntegers ℚ := by
    rw [Matrix.det_fin_two]
    exact sub_mem (mul_mem (h1 0 0) (h1 1 1)) (mul_mem (h1 0 1) (h1 1 0))
  have hdi : ((k⁻¹ : G) : Mat).det ∈ p.adicCompletionIntegers ℚ := by
    rw [Matrix.det_fin_two]
    exact sub_mem (mul_mem (h2 0 0) (h2 1 1)) (mul_mem (h2 0 1) (h2 1 0))
  have hle : ∀ x : F, x ∈ p.adicCompletionIntegers ℚ → ‖x‖ ≤ 1 := fun x hx => by
    have hv := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hx
    rw [FinitePlace.norm_def]
    exact_mod_cast (WithZeroMulInt.toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal p)).2 hv
  have hmul : ‖(k : Mat).det‖ * ‖((k⁻¹ : G) : Mat).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]
  have h1' := hle _ hd
  have h2' := hle _ hdi
  have ha : 0 ≤ ‖(k : Mat).det‖ := norm_nonneg _
  have h3 : ‖(k : Mat).det‖ * ‖((k⁻¹ : G) : Mat).det‖ ≤ ‖(k : Mat).det‖ * 1 := mul_le_mul_of_nonneg_left h2' ha
  refine le_antisymm h1' ?_
  linarith

end K2

section TI2

variable {A : Type*} [CommRing A]

def transposeInv2 (g : GL (Fin 2) A) : GL (Fin 2) A where
  val := ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)ᵀ
  inv := ((g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)ᵀ
  val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

theorem transposeInv3_mul (a b : GL (Fin 3) A) : transposeInv3 (a * b) = transposeInv3 a * transposeInv3 b := by
  refine Units.ext ?_
  show (((a * b)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ =
    (((a⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ * (((b⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem transposeInv3_transposeInv3 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  show ((((transposeInv3 g)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = (g : Matrix (Fin 3) (Fin 3) A)
  show (((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ)ᵀ = (g : Matrix (Fin 3) (Fin 3) A)
  exact Matrix.transpose_transpose _

theorem transposeInv3_iotaGL (k : GL (Fin 2) A) : transposeInv3 (iotaGL k) = iotaGL (transposeInv2 k) := by
  refine Units.ext ?_
  show ((((iotaGL k)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = embedMat2 ((transposeInv2 k : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
  rw [← map_inv, coe_iotaGL]
  show (embedMat2 (((k⁻¹ : GL (Fin 2) A)) : Matrix (Fin 2) (Fin 2) A))ᵀ =
    embedMat2 ((((k⁻¹ : GL (Fin 2) A)) : Matrix (Fin 2) (Fin 2) A)ᵀ)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.transpose_apply]

theorem dualWhittakerFn3_translate {R : Type*} (W : GL (Fin 3) A → R) (h g : GL (Fin 3) A) :
    dualWhittakerFn3 (fun x => W (x * h)) g = dualWhittakerFn3 W (g * transposeInv3 h) := by
  simp only [dualWhittakerFn3_apply]
  rw [transposeInv3_mul, transposeInv3_transposeInv3, mul_assoc]

theorem scalarPi_comm {K : Type*} [Field K] (π : K) (hπ : π ≠ 0) (g : GL (Fin 2) K) :
    scalarPi π hπ * g = g * scalarPi π hπ := by
  refine Units.ext ?_
  have h : ((scalarPi π hπ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = π • (1 : Matrix (Fin 2) (Fin 2) K) := by
    show (!![π, 0; 0, π] : Matrix (Fin 2) (Fin 2) K) = π • 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [Units.val_mul, Units.val_mul, h, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

end TI2

section K2T

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem transposeInv2_mem_K2 {k : G} (hk : k ∈ K2 p) : transposeInv2 k ∈ K2 p := by
  rw [mem_K2_iff] at hk ⊢
  obtain ⟨h1, h2⟩ := hk
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · show (((k⁻¹ : G) : Mat))ᵀ i j ∈ _
    rw [Matrix.transpose_apply]; exact h2 j i
  · show ((k : G) : Mat)ᵀ i j ∈ _
    rw [Matrix.transpose_apply]; exact h1 j i

end K2T

section Avg

set_option synthInstance.maxHeartbeats 1600000

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p))

def stab (W : G₃ → ℂ) : Subgroup G where
  carrier := {k | ∀ g : G₃, W (g * iotaGL k) = W g}
  mul_mem' := by
    intro a b ha hb g
    rw [map_mul, ← mul_assoc, hb, ha]
  one_mem' := by intro g; rw [map_one, mul_one]
  inv_mem' := by
    intro a ha g
    have := ha (g * iotaGL a⁻¹)
    rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] at this
    exact this.symm

theorem mem_stab_iff (W : G₃ → ℂ) (k : G) : k ∈ stab p W ↔ ∀ g : G₃, W (g * iotaGL k) = W g := Iff.rfl

theorem isOpen_stab {W : G₃ → ℂ}
    (hsm : ∃ Uv : Subgroup G₃, IsOpen (Uv : Set G₃) ∧ ∀ k ∈ Uv, ∀ g : G₃, W (g * k) = W g) :
    IsOpen ((stab p W : Subgroup G) : Set G) := by
  obtain ⟨Uv, hUo, hUW⟩ := hsm
  have hle : Uv.comap (iotaGL : G →* G₃) ≤ stab p W := fun k hk g => hUW _ hk g
  exact Subgroup.isOpen_mono hle (hUo.preimage (continuous_iotaGL p))

abbrev Q (W : G₃ → ℂ) : Type := ↥(K2 p) ⧸ (stab p W).subgroupOf (K2 p)

theorem finite_Q {W : G₃ → ℂ}
    (hsm : ∃ Uv : Subgroup G₃, IsOpen (Uv : Set G₃) ∧ ∀ k ∈ Uv, ∀ g : G₃, W (g * k) = W g) :
    Finite (Q p W) := by
  haveI : CompactSpace ↥(K2 p) := isCompact_iff_compactSpace.mp (isCompact_K2 p)
  refine Subgroup.quotient_finite_of_isOpen _ ?_
  exact (isOpen_stab p hsm).preimage continuous_subtype_val

def rep (W : G₃ → ℂ) (q : Q p W) : G := ((Quotient.out q : ↥(K2 p)) : G)

theorem rep_mem (W : G₃ → ℂ) (q : Q p W) : rep p W q ∈ K2 p := (Quotient.out q : ↥(K2 p)).2

def avg (W : G₃ → ℂ) [Fintype (Q p W)] : G₃ → ℂ :=
  fun g => ((Fintype.card (Q p W) : ℂ))⁻¹ * ∑ q : Q p W, W (g * iotaGL (rep p W q))

theorem avg_apply (W : G₃ → ℂ) [Fintype (Q p W)] (g : G₃) :
    avg p W g = ((Fintype.card (Q p W) : ℂ))⁻¹ * ∑ q : Q p W, W (g * iotaGL (rep p W q)) := rfl

theorem apply_mul_iotaGL_rep_smul (W : G₃ → ℂ) (k : ↥(K2 p)) (q : Q p W) (g : G₃) :
    W (g * iotaGL (rep p W (k • q))) = W (g * iotaGL ((k : G) * rep p W q)) := by

  have hq : (k • q : Q p W) = QuotientGroup.mk (k * Quotient.out q) := by
    have := MulAction.Quotient.mk_smul_out (H := (stab p W).subgroupOf (K2 p)) k q
    rw [smul_eq_mul] at this
    exact this.symm
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul ((stab p W).subgroupOf (K2 p)) (k * Quotient.out q)
  have hrep : rep p W (k • q) = (k : G) * rep p W q * ((s : ↥(K2 p)) : G) := by
    show ((Quotient.out (k • q) : ↥(K2 p)) : G) = _
    rw [hq, hs, Subgroup.coe_mul, Subgroup.coe_mul]
    rfl
  have hsS : ((s : ↥(K2 p)) : G) ∈ stab p W := Subgroup.mem_subgroupOf.mp s.2
  rw [hrep, map_mul, ← mul_assoc, hsS]

theorem avg_mul_iotaGL (W : G₃ → ℂ) [Fintype (Q p W)] {k : G} (hk : k ∈ K2 p) (g : G₃) :
    avg p W (g * iotaGL k) = avg p W g := by
  rw [avg_apply, avg_apply]
  congr 1
  have h1 : ∀ q : Q p W, W (g * iotaGL k * iotaGL (rep p W q)) = W (g * iotaGL (rep p W ((⟨k, hk⟩ : ↥(K2 p)) • q))) := by
    intro q
    rw [show g * iotaGL k * iotaGL (rep p W q) = g * iotaGL (((⟨k, hk⟩ : ↥(K2 p)) : G) * rep p W q) by
      rw [map_mul, mul_assoc]]
    exact (apply_mul_iotaGL_rep_smul p W ⟨k, hk⟩ q g).symm
  simp_rw [h1]
  exact Function.Bijective.sum_comp (MulAction.bijective (⟨k, hk⟩ : ↥(K2 p))) (fun q => W (g * iotaGL (rep p W q)))

theorem avg_mem (W : G₃ → ℂ) [Fintype (Q p W)] : avg p W ∈ gl3CyclicSubspace W := by
  have : avg p W = ((Fintype.card (Q p W) : ℂ))⁻¹ • ∑ q : Q p W, gl3AmbientRightTranslate (R := ℂ) (iotaGL (rep p W q)) W := by
    funext g
    rw [avg_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    rfl
  rw [this]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => Submodule.subset_span ⟨_, rfl⟩)

theorem dual_avg_mul_iotaGL (W : G₃ → ℂ) [Fintype (Q p W)] {k : G} (hk : k ∈ K2 p) (g : G₃) :
    dualWhittakerFn3 (avg p W) (g * iotaGL k) = dualWhittakerFn3 (avg p W) g := by
  simp only [dualWhittakerFn3_apply]
  rw [transposeInv3_mul, transposeInv3_iotaGL, ← mul_assoc, avg_mul_iotaGL p W (transposeInv2_mem_K2 p hk)]

end Avg

section RS

set_option synthInstance.maxHeartbeats 1600000

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

abbrev δ (g : G) : ℝ := (modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ)

theorem δ_pos (g : G) : 0 < δ p g := by
  show 0 < ((modulus _ : ℝ≥0) : ℝ)
  rw [coe_modulus_eq_norm]
  exact norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det g).ne_zero

theorem δ_mul (g k : G) : δ p (g * k) = δ p g * δ p k := by
  show ((modulus _ : ℝ≥0) : ℝ) = ((modulus _ : ℝ≥0) : ℝ) * ((modulus _ : ℝ≥0) : ℝ)
  rw [map_mul, Units.val_mul, modulus_mul, NNReal.coe_mul]

theorem δ_unip_mul (x : G) (hx : x ∈ unip p) (g : G) : δ p (x * g) = δ p g := by
  obtain ⟨y, rfl⟩ := hx
  rw [δ_mul]
  show ((modulus ((Matrix.GeneralLinearGroup.det (unipotentGL2 y.toAdd : G) : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ≥0) : ℝ) * δ p g = δ p g
  rw [det_unipotentGL2, Units.val_one, modulus_one, NNReal.coe_one, one_mul]

theorem continuous_δ : Continuous (δ p) := by
  have : δ p = fun g : G => ‖(g : Mat).det‖ := by
    funext g
    show ((modulus _ : ℝ≥0) : ℝ) = _
    rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
  rw [this]
  exact continuous_norm.comp (Units.continuous_val.matrix_det)

theorem δ_K2 {k : G} (hk : k ∈ K2 p) : δ p k = 1 := modulus_det_eq_one p hk

scoped instance charZero_local : CharZero F :=
  charZero_of_injective_algebraMap (algebraMap ℚ F).injective

theorem term
    [MeasurableSpace G] [BorelSpace G]
    (μ₂ : Measure G) [μ₂.IsHaarMeasure] (μN : Measure (unip p)) [μN.IsHaarMeasure] (s : ℂ)
    (A B : G → ℂ) (hA : Measurable A) (hB : Measurable B)
    (hAB : ∀ x ∈ unip p, ∀ g k : G, A (x * g) * B (x * k) = A g * B k)
    (hBK : ∀ k ∈ K2 p, ∀ g : G, B (g * k) = B g) {r : G} (hr : r ∈ K2 p)
    (hint : Integrable (fun g : G => (A g * B g) * ((δ p g : ℝ) : ℂ) ^ (s - 1 / 2))
      (μ₂.withDensity (HaarQuotient.density (unip p) μN))) :
    Integrable (fun g : G => (A (g * r) * B g) * ((δ p g : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unip p) μN)) ∧
      RSCarrier.rsLocalIntegral μ₂ (unip p) μN (δ p) s (fun g => A (g * r)) B =
        RSCarrier.rsLocalIntegral μ₂ (unip p) μN (δ p) s A B := by
  haveI : μN.IsMulRightInvariant := isMulRightInvariant_unip p μN
  haveI : μ₂.IsMulRightInvariant := Matrix.GeneralLinearGroup.isMulRightInvariant_of_isHaarMeasure_fin_two μ₂
  have hμh : Measure.map (· * r⁻¹) μ₂ = μ₂ := map_mul_right_eq_self μ₂ r⁻¹
  have H := RSCarrier.rsLocalIntegral_comp_mul_right_eq_mul_rsLocalIntegral_of_map_mul_right_eq
    μ₂ (unip p) (isClosed_unip p) μN r⁻¹ hμh (δ p) (continuous_δ p).measurable (δ_pos p) (δ_mul p)
    (δ_unip_mul p) s A B hA hB hAB
  have hBr : ∀ g : G, B (g * r⁻¹) = B g := fun g => hBK _ (inv_mem hr) g
  simp only [inv_inv, hBr] at H
  have h1 : ((δ p r : ℝ) : ℂ) ^ (s - 1 / 2) = 1 := by rw [δ_K2 p hr, Complex.ofReal_one, Complex.one_cpow]
  refine ⟨H.1.mp hint, ?_⟩
  rw [H.2, h1, one_mul]

theorem unipotent_eq_unipotentGL2 (y : F) : (unipotent y : G) = unipotentGL2 y := by
  refine Units.ext ?_
  show (!![(1 : F), y; 0, 1] : Mat) = ((unipotentGL2 y : G) : Mat)
  rw [unipotentGL2_coe]

theorem longWeyl3_mul_transposeInv3_iotaGL_unipotentGL2 (y : F) :
    (longWeyl3 : G₃) * transposeInv3 (iotaGL (unipotentGL2 y : G)) = upperUnipotent3 0 (-y) 0 * longWeyl3 := by
  refine Units.ext ?_
  have hinv : ((iotaGL (unipotentGL2 y : G))⁻¹ : G₃) = iotaGL (unipotentGL2 (-y) : G) := by
    rw [← map_inv]; congr 1
    refine Units.ext ?_
    show ((unipotentGL2 y : G)⁻¹ : G).val = _
    rw [unipotentGL2_coe]; rfl
  show (longWeyl3 : G₃).val * (((iotaGL (unipotentGL2 y : G))⁻¹ : G₃) : Matrix (Fin 3) (Fin 3) F)ᵀ =
    (upperUnipotent3 (0 : F) (-y) 0).val * (longWeyl3 : G₃).val
  rw [hinv, coe_iotaGL, unipotentGL2_coe, longWeyl3_coe]
  show (!![(0 : F), 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) F) * (embedMat2 !![(1 : F), -y; 0, 1])ᵀ =
    (!![(1 : F), 0, 0; 0, 1, -y; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) * !![(0 : F), 0, 1; 0, 1, 0; 1, 0, 0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]

theorem phase_direct {ψv : AddChar F ℂ} (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹)
    {W : G₃ → ℂ} (hW : IsGL3PsiWhittakerFn ψv W) {W₂ : G → ℂ}
    (hW₂ψ : ∀ (x : F) (g : G), W₂ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W₂ g) :
    ∀ x ∈ unip p, ∀ g k : G, W (iotaGL (x * g)) * W₂ (x * k) = W (iotaGL g) * W₂ k := by
  rintro x ⟨y, rfl⟩ g k
  show W (iotaGL ((unipotentGL2 y.toAdd : G) * g)) * W₂ ((unipotentGL2 y.toAdd : G) * k) = W (iotaGL g) * W₂ k
  rw [map_mul, iotaGL_unipotentGL2, hW, add_zero, ← unipotent_eq_unipotentGL2, hW₂ψ, hψinv, AddChar.inv_apply]
  have : NumberField.StandardAddChar.psiLocal ℚ p (-y.toAdd) * NumberField.StandardAddChar.psiLocal ℚ p y.toAdd = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  calc NumberField.StandardAddChar.psiLocal ℚ p (-y.toAdd) * W (iotaGL g) *
        (NumberField.StandardAddChar.psiLocal ℚ p y.toAdd * W₂ k)
      = (NumberField.StandardAddChar.psiLocal ℚ p (-y.toAdd) * NumberField.StandardAddChar.psiLocal ℚ p y.toAdd) *
          (W (iotaGL g) * W₂ k) := by ring
    _ = W (iotaGL g) * W₂ k := by rw [this, one_mul]

theorem phase_dual {ψv : AddChar F ℂ} (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹)
    {W : G₃ → ℂ} (hW : IsGL3PsiWhittakerFn ψv W) (z : G) {W₂d : G → ℂ}
    (hW₂dψ : ∀ (x : F) (g : G), W₂d (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ x * W₂d g) :
    ∀ x ∈ unip p, ∀ g k : G,
      dualWhittakerFn3 W (iotaGL (x * g) * iotaGL z) * W₂d (x * k) = dualWhittakerFn3 W (iotaGL g * iotaGL z) * W₂d k := by
  rintro x ⟨y, rfl⟩ g k
  show dualWhittakerFn3 W (iotaGL ((unipotentGL2 y.toAdd : G) * g) * iotaGL z) * W₂d ((unipotentGL2 y.toAdd : G) * k) =
    dualWhittakerFn3 W (iotaGL g * iotaGL z) * W₂d k
  simp only [dualWhittakerFn3_apply]
  rw [map_mul, mul_assoc (iotaGL _), transposeInv3_mul, ← mul_assoc, longWeyl3_mul_transposeInv3_iotaGL_unipotentGL2,
    mul_assoc, hW, zero_add, ← unipotent_eq_unipotentGL2, hW₂dψ, hψinv, AddChar.inv_apply, AddChar.inv_apply, neg_neg]
  have : NumberField.StandardAddChar.psiLocal ℚ p y.toAdd * NumberField.StandardAddChar.psiLocal ℚ p (-y.toAdd) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  calc NumberField.StandardAddChar.psiLocal ℚ p y.toAdd * W (longWeyl3 * transposeInv3 (iotaGL g * iotaGL z)) *
        (NumberField.StandardAddChar.psiLocal ℚ p (-y.toAdd) * W₂d k)
      = (NumberField.StandardAddChar.psiLocal ℚ p y.toAdd * NumberField.StandardAddChar.psiLocal ℚ p (-y.toAdd)) *
          (W (longWeyl3 * transposeInv3 (iotaGL g * iotaGL z)) * W₂d k) := by ring
    _ = W (longWeyl3 * transposeInv3 (iotaGL g * iotaGL z)) * W₂d k := by rw [this, one_mul]

theorem dual_avg_iotaGL_mul (W : G₃ → ℂ) [Fintype (Q p W)] (z : G) (hz : ∀ g : G, z * g = g * z) (g : G) :
    dualWhittakerFn3 (avg p W) (iotaGL g * iotaGL z) =
      ((Fintype.card (Q p W) : ℂ))⁻¹ *
        ∑ q : Q p W, dualWhittakerFn3 W (iotaGL (g * transposeInv2 (rep p W q)) * iotaGL z) := by
  rw [dualWhittakerFn3_apply, avg_apply]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  have h1 : W (longWeyl3 * transposeInv3 (iotaGL g * iotaGL z) * iotaGL (rep p W q)) =
      dualWhittakerFn3 (fun x => W (x * iotaGL (rep p W q))) (iotaGL g * iotaGL z) := by
    rw [dualWhittakerFn3_apply]
  rw [h1, dualWhittakerFn3_translate, transposeInv3_iotaGL, mul_assoc, ← map_mul, hz, map_mul, ← mul_assoc, ← map_mul]

end RS

end KAvg
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_invariant_rsLocalIntegral_eq.KAvg"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_invariant_rsLocalIntegral_eq.KAvg"

open KAvg in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (ℓ : ℕ) :
    ∃ W'' : LocalGL3 v → ℂ, W'' ∈ gl3CyclicSubspace W ∧
      (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, W'' (g * iotaGL k) = W'' g) ∧
      (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v,
        dualWhittakerFn3 W'' (g * iotaGL k) = dualWhittakerFn3 W'' g) ∧
      (letI := localGLBorel ℚ v
       haveI := borelSpace_localGLBorel ℚ v
       ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
         (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure]
         (s : ℂ),
       (∀ (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
          (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
            W₂ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
          (hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
            k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g),
          Integrable
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (W (iotaGL g) * W₂ g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                    v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) →
          Integrable
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (W'' (iotaGL g) * W₂ g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                    v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) ∧
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
              s (fun g => W (iotaGL g)) W₂ =
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
              s (fun g => W'' (iotaGL g)) W₂) ∧
       (∀ (W₂d : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
          (hW₂dψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
            W₂d (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * W₂d g)
          (hW₂dK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
            k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂d (g * k) = W₂d g),
          Integrable
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (dualWhittakerFn3 W (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                  (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                    (-(ℓ : ℤ)))) * W₂d g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                    v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) →
          Integrable
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (dualWhittakerFn3 W'' (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                  (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                    (-(ℓ : ℤ)))) * W₂d g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                    v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) ∧
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
              s (fun g => dualWhittakerFn3 W (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                  (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) W₂d =
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
              s (fun g => dualWhittakerFn3 W'' (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                  (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) W₂d)) := by
  classical
  haveI : Finite (Q v W) := finite_Q v hsm
  haveI : Fintype (Q v W) := Fintype.ofFinite _
  obtain ⟨Uv, hUo, hUW⟩ := hsm
  have hWc : Continuous W := continuous_of_rightInvariant hUo hUW
  refine ⟨avg v W, avg_mem v W, fun k hk g => avg_mul_iotaGL v W hk g, fun k hk g => dual_avg_mul_iotaGL v W hk g, ?_⟩
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := localGLBorel ℚ v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ v
  intro μ₂ _ μN _ s
  have hcard : (Fintype.card (Q v W) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcc : ((Fintype.card (Q v W) : ℂ))⁻¹ * ((Fintype.card (Q v W) : ℂ)) = 1 := inv_mul_cancel₀ hcard
  constructor
  · intro W₂ hW₂ψ hW₂K hint
    have hA : Measurable fun g : GL (Fin 2) (v.adicCompletion ℚ) => W (iotaGL g) :=
      (hWc.comp (continuous_iotaGL v)).measurable
    have hK' : ∀ k ∈ K2 v, ∀ g : GL (Fin 2) (v.adicCompletion ℚ), W₂ (g * k) = W₂ g := fun k hk g => hW₂K k g hk
    have hB : Measurable W₂ := (continuous_of_rightInvariant (isOpen_K2 v) hK').measurable
    have hAB := phase_direct v hψinv hW hW₂ψ
    have T := fun q : Q v W => term v μ₂ μN s (fun g => W (iotaGL g)) W₂ hA hB hAB hK' (rep_mem v W q) hint
    have key : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
        (avg v W (iotaGL g) * W₂ g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) =
        ((Fintype.card (Q v W) : ℂ))⁻¹ * ∑ q : Q v W, (W (iotaGL (g * rep v W q)) * W₂ g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) := by
      intro g
      rw [avg_apply]
      simp_rw [← map_mul]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring
    refine ⟨?_, ?_⟩
    · have : Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
          ((Fintype.card (Q v W) : ℂ))⁻¹ * ∑ q : Q v W, (W (iotaGL (g * rep v W q)) * W₂ g) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) :=
        (integrable_finset_sum _ fun q _ => (T q).1).const_mul _
      exact this.congr (ae_of_all _ fun g => (key g).symm)
    · symm
      show (∫ g, (avg v W (iotaGL g) * W₂ g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
          ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) = _
      simp_rw [key]
      rw [integral_const_mul, integral_finset_sum _ fun q _ => (T q).1]
      have h2 : ∀ q : Q v W, (∫ g, (W (iotaGL (g * rep v W q)) * W₂ g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
          ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) =
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => W (iotaGL g)) W₂ := fun q => (T q).2
      simp_rw [h2]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hcc, one_mul]
  · intro W₂d hW₂dψ hW₂dK hint
    set z : GL (Fin 2) (v.adicCompletion ℚ) :=
      UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)) with hz
    have hzc : ∀ g : GL (Fin 2) (v.adicCompletion ℚ), z * g = g * z := fun g =>
      ((Commute.symm (scalarPi_comm _ hπ g)).symm.zpow_left (-(ℓ : ℤ))).eq
    have hA : Measurable fun g : GL (Fin 2) (v.adicCompletion ℚ) => dualWhittakerFn3 W (iotaGL g * iotaGL z) := by
      simp only [dualWhittakerFn3_apply]
      exact (hWc.comp (continuous_const.mul (continuous_transposeInv3.comp
        ((continuous_iotaGL v).mul continuous_const)))).measurable
    have hK' : ∀ k ∈ K2 v, ∀ g : GL (Fin 2) (v.adicCompletion ℚ), W₂d (g * k) = W₂d g := fun k hk g => hW₂dK k g hk
    have hB : Measurable W₂d := (continuous_of_rightInvariant (isOpen_K2 v) hK').measurable
    have hAB := phase_dual v hψinv hW z hW₂dψ
    have T := fun q : Q v W => term v μ₂ μN s (fun g => dualWhittakerFn3 W (iotaGL g * iotaGL z)) W₂d hA hB hAB hK'
      (transposeInv2_mem_K2 v (rep_mem v W q)) hint
    have key : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
        (dualWhittakerFn3 (avg v W) (iotaGL g * iotaGL z) * W₂d g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) =
        ((Fintype.card (Q v W) : ℂ))⁻¹ * ∑ q : Q v W,
          (dualWhittakerFn3 W (iotaGL (g * transposeInv2 (rep v W q)) * iotaGL z) * W₂d g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) := by
      intro g
      rw [dual_avg_iotaGL_mul v W z hzc, ← Finset.sum_mul, ← Finset.sum_mul]
      ring
    refine ⟨?_, ?_⟩
    · have : Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
          ((Fintype.card (Q v W) : ℂ))⁻¹ * ∑ q : Q v W,
            (dualWhittakerFn3 W (iotaGL (g * transposeInv2 (rep v W q)) * iotaGL z) * W₂d g) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) :=
        (integrable_finset_sum _ fun q _ => (T q).1).const_mul _
      exact this.congr (ae_of_all _ fun g => (key g).symm)
    · symm
      show (∫ g, (dualWhittakerFn3 (avg v W) (iotaGL g * iotaGL z) * W₂d g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
          ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) = _
      simp_rw [key]
      rw [integral_const_mul, integral_finset_sum _ fun q _ => (T q).1]
      have h2 : ∀ q : Q v W, (∫ g, (dualWhittakerFn3 W (iotaGL (g * transposeInv2 (rep v W q)) * iotaGL z) * W₂d g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
          ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) =
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => dualWhittakerFn3 W (iotaGL g * iotaGL z)) W₂d := fun q => (T q).2
      simp_rw [h2]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hcc, one_mul]

end S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_invariant_rsLocalIntegral_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_invariant_rsLocalIntegral_eq (solution)
