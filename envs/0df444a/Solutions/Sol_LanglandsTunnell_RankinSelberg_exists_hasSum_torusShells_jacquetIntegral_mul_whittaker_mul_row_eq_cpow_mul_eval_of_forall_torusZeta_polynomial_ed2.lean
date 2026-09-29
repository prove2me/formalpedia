-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_hasSum_torusShells_jacquetIntegral_mul_whittaker_mul_row_eq_cpow_mul_eval_of_forall_torusZeta_polynomial_ed2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/efd86ae8-1176-51cf-9d24-3d349cd821b2

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_le_setIntegral_localLevelOne_mul_diagZ_mul_eq_zero_of_sqrt_modulus_tail_of_forall_torusZeta_polynomial
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isOpen_forall_mul_eq_of_mem_principalSeries2
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
import Theorems.Thm_AutomorphicForm_secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_hasSum_torusShells_jacquetIntegral_mul_whittaker_mul_row_eq_cpow_mul_eval_of_forall_torusZeta_polynomial_ed2

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace ABSP

open Filter Topology NumberField.StandardAddChar

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)
local notation "K₀" => AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤

theorem borelSpace_units [MeasurableSpace F] [BorelSpace F] : BorelSpace Fˣ := by
  constructor
  have h1 : (Units.instMeasurableSpace : MeasurableSpace Fˣ) = MeasurableSpace.comap Units.val (borel F) := by
    rw [← ‹BorelSpace F›.measurable_eq]; rfl
  rw [h1, ← borel_comap]
  congr 1
  exact (Units.isEmbedding_val₀ (G₀ := F)).eq_induced.symm

theorem secondCountableTopology_units : SecondCountableTopology Fˣ :=
  (Units.isEmbedding_val₀ (G₀ := F)).secondCountableTopology

theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := ⟨rfl⟩
  have hN : (0 : NNReal) < (Ideal.absNorm p.asIdeal : NNReal) := by
    have h0 : Ideal.absNorm p.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact p.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero h0
  unfold selfDualHaarAt
  exact Measure.IsAddHaarMeasure.nnreal_smul _ (NNReal.rpow_pos hN).ne'

theorem norm_psiLocal (x : F) : ‖psiLocal ℚ p x‖ = 1 := by

  have key : ∀ y : F, ‖psiLocal ℚ p y‖ ≤ 1 := by
    intro y
    obtain ⟨n, hn⟩ := exists_valued_le_exp p y
    have hK : IsCompact {z : F | Valued.v (z - 0) ≤ WithZero.exp (-(-(n : ℤ)))} := isCompact_setOf_valued_sub_le p 0 _
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn ((continuous_psiLocal (K := ℚ) (v := p)).continuousOn)
    have hpow : ∀ m : ℕ, ‖psiLocal ℚ p y‖ ^ m ≤ M := by
      intro m
      have hmem : (m : F) * y ∈ {z : F | Valued.v (z - 0) ≤ WithZero.exp (-(-(n : ℤ)))} := by
        simp only [Set.mem_setOf_eq, sub_zero, neg_neg, Valuation.map_mul]
        calc Valued.v (m : F) * Valued.v y ≤ 1 * WithZero.exp (n : ℤ) := by
              refine mul_le_mul' ?_ hn
              have h := IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := ℚ) p (m : 𝓞 ℚ)
              rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at h
              simpa [map_natCast] using h
          _ = WithZero.exp (n : ℤ) := one_mul _
      have := hM _ hmem
      rwa [show psiLocal ℚ p ((m : F) * y) = psiLocal ℚ p y ^ m by
        rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow], norm_pow] at this
    by_contra hgt
    rw [not_le] at hgt
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt M hgt
    exact absurd (hpow m) (not_le.mpr hm)
  have h1 := key x
  have h2 := key (-x)
  have hprod : psiLocal ℚ p x * psiLocal ℚ p (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hx0 : ‖psiLocal ℚ p x‖ ≠ 0 := by
    intro h0
    have := congrArg norm hprod
    rw [norm_mul, h0, zero_mul, norm_one] at this
    exact zero_ne_one this
  have : ‖psiLocal ℚ p x‖ * ‖psiLocal ℚ p (-x)‖ = 1 := by rw [← norm_mul, hprod, norm_one]
  nlinarith [norm_nonneg (psiLocal ℚ p x), norm_nonneg (psiLocal ℚ p (-x))]

theorem isLocallyConstant_of_open_stabiliser {f : G2 → ℂ} (U : Subgroup G2) (hU : IsOpen (U : Set G2))
    (hinv : ∀ k ∈ U, ∀ g : G2, f (g * k) = f g) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hopen : IsOpen ((fun u : G2 => g * u) '' (U : Set G2)) := (isOpenMap_mul_left g) _ hU
  have hmem : g ∈ (fun u : G2 => g * u) '' (U : Set G2) := ⟨1, U.one_mem, mul_one g⟩
  filter_upwards [hopen.mem_nhds hmem] with x hx
  obtain ⟨u, hu, rfl⟩ := hx
  exact hinv u hu g

theorem exists_forall_higherUnitsAt_eq_one (χ : Fˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ c : ℕ, ∀ u ∈ higherUnitsAt ℚ p c, χ u = 1 := by
  have hO : IsOpen {u : Fˣ | χ u = 1} := hχ.isOpen_fiber 1
  obtain ⟨U, hU, hUO⟩ := (Units.isEmbedding_val₀ (G₀ := F)).isInducing.isOpen_iff.mp hO
  have h1U : (1 : F) ∈ U := by
    have h1 : (1 : Fˣ) ∈ Units.val ⁻¹' U := by
      rw [hUO]
      simp only [Set.mem_setOf_eq, map_one]
    simpa using h1
  obtain ⟨j, hj⟩ := exists_setOf_valued_sub_le_subset_of_isOpen p hU h1U
  refine ⟨j.toNat + 1, fun u hu => ?_⟩
  have hu2 := hu.2
  rcases hu2 with h0 | hle
  · omega
  have hle' : Valued.v ((u : F) - 1) ≤ WithZero.exp (-j) := by
    refine hle.trans (WithZero.exp_le_exp.mpr ?_)
    have := Int.self_le_toNat j
    push_cast
    omega
  have hmem : u ∈ Units.val ⁻¹' U := hj hle'
  rw [hUO] at hmem
  exact hmem

theorem isOpen_valued_le_exp (n : ℕ) :
    IsOpen {x : F | Valued.v x ≤ WithZero.exp (n : ℤ)} := by
  have h : {x : F | Valued.v x ≤ WithZero.exp (n : ℤ)}
      = {x : F | Valued.v (x - 0) ≤ WithZero.exp (- -(n : ℤ))} := by
    simp only [sub_zero, neg_neg]
  rw [h]
  exact (isClopen_setOf_valued_sub_le p 0 (-(n : ℤ))).isOpen

theorem exists_forall_valued_le_of_isCompact {S : Set F} (hS : IsCompact S) :
    ∃ R : ℤ, ∀ x ∈ S, Valued.v x ≤ WithZero.exp R := by
  have hcov : S ⊆ ⋃ n : ℕ, {x : F | Valued.v x ≤ WithZero.exp (n : ℤ)} := by
    intro x _
    obtain ⟨n, hn⟩ := exists_valued_le_exp p x
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  have hdir : Directed (· ⊆ ·) fun n : ℕ => {x : F | Valued.v x ≤ WithZero.exp (n : ℤ)} := by
    intro a b
    refine ⟨max a b, fun x hx => ?_, fun x hx => ?_⟩
    · exact le_trans hx (WithZero.exp_le_exp.mpr (Nat.cast_le.mpr (le_max_left a b)))
    · exact le_trans hx (WithZero.exp_le_exp.mpr (Nat.cast_le.mpr (le_max_right a b)))
  obtain ⟨n, hn⟩ := hS.elim_directed_cover _ (isOpen_valued_le_exp p) hcov hdir
  exact ⟨n, fun x hx => hn hx⟩

theorem unipotent_eq_unipotentGL2 (x : F) : (unipotent x : G2) = unipotentGL2 x :=
  Units.ext rfl

theorem diagUnits2_eq_diagonal2 (a₁ a₂ : Fˣ) : (diagUnits2 a₁ a₂ : G2) = diagonal2 p ![a₁, a₂] := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagUnits2, diagonal2, Matrix.diagonal]

theorem unipotent_mul_apply_one (x : F) (g : G2) (j : Fin 2) :
    ((unipotent x * g : G2) : Matrix (Fin 2) (Fin 2) F) 1 j = (g : Matrix (Fin 2) (Fin 2) F) 1 j := by
  rw [unipotent_eq_unipotentGL2, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp [unipotentGL2_coe]

theorem det_unipotent_mul (x : F) (g : G2) :
    Matrix.GeneralLinearGroup.det (unipotent x * g) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul]
  have : Matrix.GeneralLinearGroup.det (unipotent x : G2) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, unipotent_eq_unipotentGL2, unipotentGL2_coe, Matrix.det_fin_two_of]
    simp
  rw [this, one_mul]

theorem diagUnits2_mul_apply_one (a₁ a₂ : Fˣ) (k : G2) (j : Fin 2) :
    ((diagUnits2 a₁ a₂ * k : G2) : Matrix (Fin 2) (Fin 2) F) 1 j = (a₂ : F) * (k : Matrix (Fin 2) (Fin 2) F) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp [coe_diagUnits2]

theorem det_diagUnits2_mul (a₁ a₂ : Fˣ) (k : G2) :
    ((Matrix.GeneralLinearGroup.det (diagUnits2 a₁ a₂ * k) : Fˣ) : F) =
      (a₁ : F) * (a₂ : F) * ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) := by
  rw [map_mul, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, coe_diagUnits2, Matrix.det_fin_two_of]
  simp

theorem valued_apply_le_one_of_mem {k : G2} (hk : k ∈ K₀) (i j : Fin 2) :
    Valued.v ((k : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1 := by
  have h := hk
  rw [AdelicDock.mem_localLevelOne_iff] at h
  exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h.1.integral i j)

theorem valued_inv_apply_le_one_of_mem {k : G2} (hk : k ∈ K₀) (i j : Fin 2) :
    Valued.v (((k⁻¹ : G2) : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1 := by
  have h := hk
  rw [AdelicDock.mem_localLevelOne_iff] at h
  exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h.2.integral i j)

theorem valued_det_le_one_of_forall {m : Matrix (Fin 2) (Fin 2) F} (h : ∀ i j, Valued.v (m i j) ≤ 1) :
    Valued.v m.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
  · rw [Valuation.map_mul]; exact mul_le_one' (h 0 0) (h 1 1)
  · rw [Valuation.map_mul]; exact mul_le_one' (h 0 1) (h 1 0)

theorem valued_det_eq_one_of_mem {k : G2} (hk : k ∈ K₀) :
    Valued.v ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) = 1 := by
  have h1 : Valued.v ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) ≤ 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact valued_det_le_one_of_forall p (valued_apply_le_one_of_mem p hk)
  have h2 : Valued.v ((Matrix.GeneralLinearGroup.det k⁻¹ : Fˣ) : F) ≤ 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact valued_det_le_one_of_forall p (valued_inv_apply_le_one_of_mem p hk)
  have hprod : Valued.v ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) *
      Valued.v ((Matrix.GeneralLinearGroup.det k⁻¹ : Fˣ) : F) = 1 := by
    rw [← Valuation.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, map_one]
  refine le_antisymm h1 ?_
  by_contra hlt
  rw [not_le] at hlt
  have : Valued.v ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) *
      Valued.v ((Matrix.GeneralLinearGroup.det k⁻¹ : Fˣ) : F) < 1 :=
    calc Valued.v ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) *
          Valued.v ((Matrix.GeneralLinearGroup.det k⁻¹ : Fˣ) : F)
        ≤ Valued.v ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) * 1 := mul_le_mul_right h2 _
      _ = Valued.v ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) := mul_one _
      _ < 1 := hlt
  rw [hprod] at this
  exact lt_irrefl _ this

theorem norm_det_eq_one_of_mem {k : G2} (hk : k ∈ K₀) :
    ‖((Matrix.GeneralLinearGroup.det k : Fˣ) : F)‖ = 1 := by
  have h := valued_det_eq_one_of_mem p hk
  rw [NumberField.FinitePlace.norm_def, h, map_one]
  rfl

theorem exists_valued_row_eq_one_of_mem {k : G2} (hk : k ∈ K₀) :
    ∃ j : Fin 2, Valued.v ((k : Matrix (Fin 2) (Fin 2) F) 1 j) = 1 := by
  by_contra hne
  push Not at hne
  have hlt : ∀ j : Fin 2, Valued.v ((k : Matrix (Fin 2) (Fin 2) F) 1 j) < 1 := fun j =>
    lt_of_le_of_ne (valued_apply_le_one_of_mem p hk 1 j) (hne j)
  have hdet := valued_det_eq_one_of_mem p hk
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at hdet
  have : Valued.v ((k : Matrix (Fin 2) (Fin 2) F) 0 0 * (k : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (k : Matrix (Fin 2) (Fin 2) F) 0 1 * (k : Matrix (Fin 2) (Fin 2) F) 1 0) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
    · rw [Valuation.map_mul]
      calc Valued.v ((k : Matrix (Fin 2) (Fin 2) F) 0 0) * Valued.v ((k : Matrix (Fin 2) (Fin 2) F) 1 1)
          ≤ 1 * Valued.v ((k : Matrix (Fin 2) (Fin 2) F) 1 1) := mul_le_mul_left (valued_apply_le_one_of_mem p hk 0 0) _
        _ < 1 := by rw [one_mul]; exact hlt 1
    · rw [Valuation.map_mul]
      calc Valued.v ((k : Matrix (Fin 2) (Fin 2) F) 0 1) * Valued.v ((k : Matrix (Fin 2) (Fin 2) F) 1 0)
          ≤ 1 * Valued.v ((k : Matrix (Fin 2) (Fin 2) F) 1 0) := mul_le_mul_left (valued_apply_le_one_of_mem p hk 0 1) _
        _ < 1 := by rw [one_mul]; exact hlt 0
  rw [hdet] at this
  exact lt_irrefl _ this

def rho : @Measure Fˣ (@Units.instMeasurableSpace F _ (localBorel ℚ p)) := by
  letI := localBorel ℚ p
  exact Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))

def shell (n : ℤ) : Set Fˣ := {y : Fˣ | Valued.v (y : F) = WithZero.exp (-(n))}

theorem iUnion_shell : ⋃ n : ℤ, shell p n = Set.univ := by
  obtain ⟨-, huniq, -⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p
  ext y
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  obtain ⟨n, hn, -⟩ := huniq y
  exact ⟨n, hn⟩

theorem pairwise_disjoint_shell : Pairwise (Function.onFun Disjoint (shell p)) := by
  intro m n hmn
  refine Set.disjoint_left.mpr fun y hym hyn => hmn ?_
  simp only [shell, Set.mem_setOf_eq] at hym hyn
  have := hym.symm.trans hyn
  have := WithZero.exp_injective this
  omega

theorem measurableSet_shell (n : ℤ) :
    @MeasurableSet Fˣ (@Units.instMeasurableSpace F _ (localBorel ℚ p)) (shell p n) := by
  obtain ⟨hmeas, -⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p
  exact hmeas n

theorem rho_shell (n : ℤ) : rho p (shell p n) = rho p (shell p 0) := by
  obtain ⟨-, -, hmass, -⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p
  have := (hmass n).1
  simpa [rho, shell] using this

theorem rho_shell_lt_top : rho p (shell p 0) < ⊤ := by
  obtain ⟨-, -, hmass, -⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p
  have := (hmass 0).2.2
  simpa [rho, shell] using this

theorem norm_eq_of_mem_shell {n : ℤ} {y : Fˣ} (hy : y ∈ shell p n) :
    ‖(y : F)‖ = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-n) := by
  obtain ⟨-, -, -, hmod, -⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p
  have h := hmod n y hy
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm] at h
  simpa using h

theorem sigmaFinite_rho : SigmaFinite (rho p) := by
  refine Measure.sigmaFinite_of_countable (Set.countable_range (shell p)) ?_ ?_
  · rintro s ⟨n, rfl⟩
    rw [rho_shell]
    exact rho_shell_lt_top p
  · rw [Set.sUnion_range, iUnion_shell]

theorem lintegral_rho_eq_tsum (g : ℤ → ENNReal) (Gf : Fˣ → ENNReal)
    (hG : ∀ (n : ℤ) (t : Fˣ), t ∈ shell p n → Gf t = g n) :
    ∫⁻ t, Gf t ∂(rho p) = ∑' n : ℤ, g n * rho p (shell p 0) := by
  letI := localBorel ℚ p
  have h1 : ∫⁻ t, Gf t ∂(rho p) = ∫⁻ t in ⋃ n : ℤ, shell p n, Gf t ∂(rho p) := by
    rw [iUnion_shell, Measure.restrict_univ]
  rw [h1, lintegral_iUnion (measurableSet_shell p) (pairwise_disjoint_shell p)]
  refine tsum_congr fun n => ?_
  rw [setLIntegral_congr_fun (measurableSet_shell p n) (fun t ht => hG n t ht), setLIntegral_const, rho_shell]

theorem tsum_shift (g : ℤ → ENNReal) (n₂ : ℤ) (c : ENNReal) :
    ∑' n : ℤ, g (n - n₂) * c = ∑' n : ℤ, g n * c :=
  (Equiv.subRight n₂).tsum_eq (fun n => g n * c)

def Zf (γ : ℝ) (M : ℤ) (t : Fˣ) : ENNReal :=
  if Valued.v (t : F) ≤ WithZero.exp M then ENNReal.ofReal (‖(t : F)‖ ^ γ) else 0

def zg (γ : ℝ) (M : ℤ) (n : ℤ) : ENNReal :=
  if -M ≤ n then ENNReal.ofReal ((((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-n)) ^ γ) else 0

theorem Zf_eq_zg (γ : ℝ) (M n : ℤ) (t : Fˣ) (ht : t ∈ shell p n) : Zf p γ M t = zg p γ M n := by
  have hv : Valued.v (t : F) = WithZero.exp (-n) := ht
  have hiff : Valued.v (t : F) ≤ WithZero.exp M ↔ -M ≤ n := by rw [hv, WithZero.exp_le_exp]; omega
  unfold Zf zg
  rw [norm_eq_of_mem_shell p ht]
  by_cases h : -M ≤ n
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

theorem one_lt_absNorm : (1 : ℝ) < ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p
  exact_mod_cast this

theorem tsum_geometric_int_lt_top (c r : ENNReal) (hc : c ≠ ⊤) (hr : r < 1) (M : ℤ) :
    ∑' n : ℤ, (if -M ≤ n then c * r ^ (n + M).toNat else 0) < ⊤ := by
  have hinj : Function.Injective fun j : ℕ => (-M + j : ℤ) := fun a b h => by simpa using h
  have hsupp : Function.support (fun n : ℤ => if -M ≤ n then c * r ^ (n + M).toNat else 0) ⊆
      Set.range fun j : ℕ => (-M + j : ℤ) := by
    intro n hn
    rw [Function.mem_support] at hn
    have hle : -M ≤ n := by
      by_contra h
      exact hn (if_neg h)
    refine ⟨(n + M).toNat, ?_⟩
    show (-M + ((n + M).toNat : ℤ)) = n
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  rw [← hinj.tsum_eq hsupp]
  have : (fun j : ℕ => (if -M ≤ (-M + j : ℤ) then c * r ^ ((-M + j : ℤ) + M).toNat else 0)) = fun j : ℕ => c * r ^ j := by
    funext j
    rw [if_pos (by omega)]
    congr 2
    have : (-M + (j : ℤ) + M) = (j : ℤ) := by ring
    rw [this, Int.toNat_natCast]
  rw [this, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  exact ENNReal.mul_lt_top hc.lt_top (ENNReal.inv_lt_top.mpr (tsub_pos_iff_lt.mpr hr))

theorem real_aux {Q : ℝ} (hQ : 0 < Q) (M n : ℤ) (h : -M ≤ n) :
    Q ^ (-(n : ℝ)) = Q ^ (M : ℝ) * (Q⁻¹) ^ (n + M).toNat := by
  have hk : ((n + M).toNat : ℝ) = (n : ℝ) + M := by
    have : ((n + M).toNat : ℤ) = n + M := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  rw [inv_pow, ← Real.rpow_natCast, hk, ← Real.rpow_neg (hQ.le), ← Real.rpow_add hQ]
  congr 1
  ring

theorem zg_eq (γ : ℝ) (M n : ℤ) :
    zg p γ M n = if -M ≤ n then
      ENNReal.ofReal ((((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ γ) ^ (M : ℝ)) *
        (ENNReal.ofReal ((((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ γ)⁻¹)) ^ (n + M).toNat else 0 := by
  simp only [zg]
  split_ifs with h
  · have hq : (0 : ℝ) < ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := zero_lt_one.trans (one_lt_absNorm p)
    have hqγ : (0 : ℝ) < (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ γ) := Real.rpow_pos_of_pos hq γ
    have e1 : (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-n : ℤ)) ^ γ =
        (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ γ) ^ (-(n : ℝ)) := by
      rw [← Real.rpow_intCast, ← Real.rpow_mul hq.le, mul_comm, Real.rpow_mul hq.le]
      simp only [Int.cast_neg]
    rw [e1, real_aux hqγ M n h, ENNReal.ofReal_mul (Real.rpow_nonneg hqγ.le _),
      ENNReal.ofReal_pow (inv_nonneg.mpr hqγ.le)]
  · rfl

theorem tsum_zg_lt_top {γ : ℝ} (hγ : 0 < γ) (M : ℤ) : ∑' n : ℤ, zg p γ M n * rho p (shell p 0) < ⊤ := by
  have hq1 := one_lt_absNorm p
  have hr : ENNReal.ofReal ((((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ γ)⁻¹) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hq1 hγ)
  have heq : (fun n : ℤ => zg p γ M n * rho p (shell p 0)) = fun n : ℤ => (if -M ≤ n then
      (ENNReal.ofReal ((((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ γ) ^ (M : ℝ)) * rho p (shell p 0)) *
        (ENNReal.ofReal ((((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ γ)⁻¹)) ^ (n + M).toNat else 0) := by
    funext n
    rw [zg_eq]
    split_ifs
    · ring
    · rw [zero_mul]
  rw [heq]
  exact tsum_geometric_int_lt_top _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (rho_shell_lt_top p).ne) hr M

theorem lintegral_Zf_mul_inv_eq (γ : ℝ) (M : ℤ) (a : Fˣ) :
    ∫⁻ t, Zf p γ M (t * a⁻¹) ∂(rho p) = ∑' n : ℤ, zg p γ M n * rho p (shell p 0) := by
  obtain ⟨-, huniq, -⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p
  obtain ⟨n₂, hn₂, -⟩ := huniq a
  have hn₂' : Valued.v (a : F) = WithZero.exp (-n₂) := hn₂
  rw [lintegral_rho_eq_tsum p (fun n => zg p γ M (n - n₂)) (fun t => Zf p γ M (t * a⁻¹)) ?_]
  · exact tsum_shift (zg p γ M) n₂ _
  · intro n t ht
    apply Zf_eq_zg
    have ht' : Valued.v (t : F) = WithZero.exp (-n) := ht
    show Valued.v (((t * a⁻¹ : Fˣ) : F)) = WithZero.exp (-(n - n₂))
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Valuation.map_mul, map_inv₀, ht', hn₂', ← WithZero.exp_neg,
      ← WithZero.exp_add]
    congr 1
    ring

theorem lintegral_Zf_eq (γ : ℝ) (M : ℤ) :
    ∫⁻ t, Zf p γ M t ∂(rho p) = ∑' n : ℤ, zg p γ M n * rho p (shell p 0) := by
  have := lintegral_Zf_mul_inv_eq p γ M 1
  simpa using this

theorem measurable_Zf (γ : ℝ) (M : ℤ) :
    @Measurable Fˣ ENNReal (@Units.instMeasurableSpace F _ (localBorel ℚ p)) _ (Zf p γ M) := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  have hval : Measurable (Units.val : Fˣ → F) := fun s hs => ⟨s, hs, rfl⟩
  have hset : MeasurableSet {t : Fˣ | Valued.v (t : F) ≤ WithZero.exp M} := by
    have : {t : Fˣ | Valued.v (t : F) ≤ WithZero.exp M} = Units.val ⁻¹' {x : F | Valued.v (x - 0) ≤ WithZero.exp (- -M)} := by
      ext t; simp
    rw [this]
    exact hval (isClopen_setOf_valued_sub_le p 0 (-M)).isClosed.measurableSet
  refine Measurable.ite hset ?_ measurable_const
  exact ENNReal.measurable_ofReal.comp ((continuous_norm.measurable.comp hval).pow_const γ)

theorem continuous_unipotentGL2 : Continuous fun x : F => (unipotentGL2 x : G2) := by
  have hval : Continuous fun x : F => ((unipotentGL2 x : G2) : Matrix (Fin 2) (Fin 2) F) := by
    refine continuous_matrix ?_
    intro i j
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe] <;> fun_prop
  rw [Units.continuous_iff]
  refine ⟨hval, ?_⟩
  have : (fun x : F => (((unipotentGL2 x : G2)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) F)) =
      (fun x : F => ((unipotentGL2 x : G2) : Matrix (Fin 2) (Fin 2) F)) ∘ (fun x : F => -x) := by
    funext x
    simp only [Function.comp_apply]
    rw [show (unipotentGL2 (-x) : G2) = (unipotentGL2 x)⁻¹ from by
      apply eq_inv_of_mul_eq_one_left
      rw [← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]]
  rw [this]
  exact hval.comp continuous_neg

theorem continuous_diagUnits2 : Continuous fun a : Fˣ × Fˣ => (diagUnits2 a.1 a.2 : G2) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [coe_diagUnits2]
    · exact Units.continuous_val.comp continuous_fst
    · exact continuous_const
    · exact continuous_const
    · exact Units.continuous_val.comp continuous_snd
  · have : ∀ a : Fˣ × Fˣ, (((diagUnits2 a.1 a.2 : G2)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) F) =
        !![((a.1⁻¹ : Fˣ) : F), 0; 0, ((a.2⁻¹ : Fˣ) : F)] := fun a => rfl
    simp_rw [this]
    refine continuous_matrix fun i j => ?_
    have h1 : Continuous fun a : Fˣ × Fˣ => ((a.1⁻¹ : Fˣ) : F) :=
      Units.continuous_val.comp (continuous_inv.comp continuous_fst)
    have h2 : Continuous fun a : Fˣ × Fˣ => ((a.2⁻¹ : Fˣ) : F) :=
      Units.continuous_val.comp (continuous_inv.comp continuous_snd)
    fin_cases i <;> fin_cases j
    · simpa using h1
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa using h2

theorem diagOne_eq_diagUnits2 (a : Fˣ) : (diagOne a : G2) = diagUnits2 a 1 := by
  apply Units.ext
  rw [coe_diagUnits2]
  show Matrix.diagonal ![(a : F), 1] = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem continuous_diagOne : Continuous fun a : Fˣ => (diagOne a : G2) := by
  have : (fun a : Fˣ => (diagOne a : G2)) = fun a => diagUnits2 a 1 := funext (diagOne_eq_diagUnits2 p)
  rw [this]
  exact (continuous_diagUnits2 p).comp (continuous_id.prodMk continuous_const)

theorem diagZ_mul_diagUnits2_one (ϖ : Fˣ) (d : ℤ) (u : Fˣ) :
    (diagZ (ϖ : F) ϖ.ne_zero d * diagUnits2 u 1 : G2) = diagOne (ϖ ^ d * u) := by
  apply Units.ext
  rw [Units.val_mul]
  have h1 : ((diagZ (ϖ : F) ϖ.ne_zero d : G2) : Matrix (Fin 2) (Fin 2) F) = !![(ϖ : F) ^ d, 0; 0, 1] := rfl
  have h2 : ((diagOne (ϖ ^ d * u) : G2) : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![((ϖ ^ d * u : Fˣ) : F), 1] := rfl
  rw [h1, h2, coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_zpow_eq_zpow_val]

theorem diagZ_eq_diagOne (ϖ : Fˣ) (d : ℤ) : (diagZ (ϖ : F) ϖ.ne_zero d : G2) = diagOne (ϖ ^ d) := by
  have := diagZ_mul_diagUnits2_one p ϖ d 1
  rwa [mul_one, show (diagUnits2 (1 : Fˣ) 1 : G2) = 1 from by
    apply Units.ext; rw [coe_diagUnits2]; ext i j; fin_cases i <;> fin_cases j <;> simp, mul_one] at this

theorem diagUnits2_one_mul_apply_one (u : Fˣ) (k : G2) (j : Fin 2) :
    ((diagUnits2 u 1 * k : G2) : Matrix (Fin 2) (Fin 2) F) 1 j = (k : Matrix (Fin 2) (Fin 2) F) 1 j := by
  rw [diagUnits2_mul_apply_one]; simp

theorem isLocalLevelOne_top_of_integral {m : Matrix (Fin 2) (Fin 2) F} (h : ∀ i j, Valued.v (m i j) ≤ 1) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m := by
  refine ⟨fun i j => (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h i j), ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]; exact h 1 0
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : F)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le (h 1 1) (by simp)

theorem diagUnits2_unit_mem {u : Fˣ} (hu : Valued.v (u : F) = 1) : (diagUnits2 u 1 : G2) ∈ K₀ := by
  rw [AdelicDock.mem_localLevelOne_iff]
  have hu' : Valued.v (((u⁻¹ : Fˣ)) : F) = 1 := by rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  constructor
  · refine isLocalLevelOne_top_of_integral p fun i j => ?_
    rw [coe_diagUnits2]
    fin_cases i <;> fin_cases j <;> simp [hu]
  · refine isLocalLevelOne_top_of_integral p fun i j => ?_
    have : (((diagUnits2 u 1 : G2)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) F) = !![((u⁻¹ : Fˣ) : F), 0; 0, ((1⁻¹ : Fˣ) : F)] := rfl
    rw [this]
    fin_cases i <;> fin_cases j <;> simp [hu, hu']

theorem setIntegral_K0_mul_left_eq [MeasurableSpace G2] [BorelSpace G2] (μ₂ : Measure G2) [μ₂.IsMulLeftInvariant]
    (f : G2 → ℂ) {t : G2} (ht : t ∈ K₀) :
    ∫ k in ((K₀ : Subgroup G2) : Set G2), f (t * k) ∂μ₂ = ∫ k in ((K₀ : Subgroup G2) : Set G2), f k ∂μ₂ := by
  have hK₀m : MeasurableSet ((K₀ : Subgroup G2) : Set G2) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ top_ne_bot).2.measurableSet
  rw [← integral_indicator hK₀m, ← integral_indicator hK₀m]
  have h : (fun k : G2 => ((K₀ : Subgroup G2) : Set G2).indicator (fun k => f (t * k)) k) =
      fun k : G2 => ((K₀ : Subgroup G2) : Set G2).indicator f (t * k) := by
    funext k
    by_cases hk : k ∈ ((K₀ : Subgroup G2) : Set G2)
    · rw [Set.indicator_of_mem hk, Set.indicator_of_mem (Subgroup.mul_mem _ ht hk)]
    · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem]
      intro htk
      exact hk (by simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ ht) htk)
  rw [h]
  exact integral_mul_left_eq_self _ t

namespace SpanAux
section Generic

variable {G : Type*} [Group G]

theorem translate_mem_span (f : G → ℂ) (h : G) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    (fun g : G => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h')) := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h', rfl⟩ := hWm
      exact Submodule.subset_span ⟨h * h', funext fun g => by simp only [mul_assoc]⟩
  | zero => exact Submodule.zero_mem _
  | add W₁ W₂ _ _ h₁ h₂ =>
      have : (fun g : G => (W₁ + W₂) (g * h)) = (fun g : G => W₁ (g * h)) + fun g : G => W₂ (g * h) := rfl
      rw [this]; exact Submodule.add_mem _ h₁ h₂
  | smul a W _ h₁ =>
      have : (fun g : G => (a • W) (g * h)) = a • fun g : G => W (g * h) := rfl
      rw [this]; exact Submodule.smul_mem _ a h₁

theorem span_le_span_of_mem (f W₀ : G → ℂ)
    (h₀ : f ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => W₀ (g * h'))) :
    Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h')) ≤
      Submodule.span ℂ (Set.range fun h' : G => fun g : G => W₀ (g * h')) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨h, rfl⟩
  exact translate_mem_span W₀ h h₀

theorem law_of_mem_span (f : G → ℂ) (a : G) (χ : ℂ) (hf : ∀ g : G, f (a * g) = χ * f g) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    ∀ g : G, W (a * g) = χ * W g := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h', rfl⟩ := hWm
      intro g
      show f (a * g * h') = χ * f (g * h')
      rw [mul_assoc, hf]
  | zero => intro g; simp
  | add W₁ W₂ _ _ h₁ h₂ => intro g; simp only [Pi.add_apply, h₁ g, h₂ g]; ring
  | smul c W _ h₁ => intro g; simp only [Pi.smul_apply, smul_eq_mul, h₁ g]; ring

variable [TopologicalSpace G] [ContinuousMul G]

theorem exists_open_stabilizer_of_mem_span (f : G → ℂ) (K : Subgroup G) (hK : IsOpen (K : Set G))
    (hf : ∀ k ∈ K, ∀ g : G, f (g * k) = f g) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h, rfl⟩ := hWm
      refine ⟨K.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
      · have hc : Continuous fun k : G => h⁻¹ * k * h⁻¹⁻¹ :=
          (continuous_const.mul continuous_id).mul continuous_const
        have hset : ((K.comap (MulAut.conj h⁻¹).toMonoidHom : Subgroup G) : Set G) =
            (fun k : G => h⁻¹ * k * h⁻¹⁻¹) ⁻¹' (K : Set G) := by
          ext k
          simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            SetLike.mem_coe]
        rw [hset]
        exact hK.preimage hc
      · intro k hk g
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hk
        show f (g * k * h) = f (g * h)
        rw [show g * k * h = g * h * (h⁻¹ * k * h) by simp only [mul_assoc, mul_inv_cancel_left]]
        exact hf _ hk (g * h)
  | zero => exact ⟨⊤, by simp, fun _ _ _ => rfl⟩
  | add W₁ W₂ _ _ h₁ h₂ =>
      obtain ⟨U₁, hU₁, hW₁⟩ := h₁
      obtain ⟨U₂, hU₂, hW₂⟩ := h₂
      refine ⟨U₁ ⊓ U₂, ?_, ?_⟩
      · rw [Subgroup.coe_inf]; exact hU₁.inter hU₂
      · intro k hk g
        rw [Subgroup.mem_inf] at hk
        simp only [Pi.add_apply, hW₁ k hk.1 g, hW₂ k hk.2 g]
  | smul c W _ h₁ =>
      obtain ⟨U, hU, hWU⟩ := h₁
      exact ⟨U, hU, fun k hk g => by simp only [Pi.smul_apply, hWU k hk g]⟩

end Generic

end SpanAux

end ABSP

noncomputable section

namespace RowCutoff47

open IsDedekindDomain NumberField
open scoped WithZero

section Valuation

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem exists_uniformizer :
    ∃ ϖ : v.adicCompletion K, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer K v
  exact ⟨((WithVal.equiv (HeightOneSpectrum.valuation K v)).symm π : v.adicCompletion K),
    by rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ⟩

variable {K v}

theorem uniformizer_ne_zero {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) :
    ϖ ≠ 0 := by
  intro h; rw [h, Valuation.map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm

theorem v_uniformizer_zpow {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (j : ℤ) : Valued.v (ϖ ^ j) = WithZero.exp (-j) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem v_uniformizer_pow {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (n : ℕ) : Valued.v (ϖ ^ n) = WithZero.exp (-(n : ℤ)) := by
  rw [← zpow_natCast, v_uniformizer_zpow hϖ]

theorem v_add_le {x y : v.adicCompletion K} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x + y) ≤ γ :=
  (Valuation.map_add _ x y).trans (max_le hx hy)

theorem v_sub_le {x y : v.adicCompletion K} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x - y) ≤ γ := by
  rw [sub_eq_add_neg]; exact v_add_le hx (by rwa [Valuation.map_neg])

theorem v_mul_le {x y : v.adicCompletion K} {a b : ℤ} (hx : Valued.v x ≤ WithZero.exp a)
    (hy : Valued.v y ≤ WithZero.exp b) : Valued.v (x * y) ≤ WithZero.exp (a + b) := by
  rw [Valuation.map_mul, WithZero.exp_add]
  exact mul_le_mul' hx hy

theorem exp_neg_succ_lt_one (n : ℕ) : WithZero.exp (-((n : ℤ) + 1)) < (1 : ℤᵐ⁰) := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

theorem exp_neg_succ_le_one (n : ℕ) : WithZero.exp (-((n : ℤ) + 1)) ≤ (1 : ℤᵐ⁰) :=
  (exp_neg_succ_lt_one n).le

theorem exp_antitone_succ (n : ℕ) :
    WithZero.exp (-(((n + 1 : ℕ) : ℤ) + 1)) ≤ WithZero.exp (-((n : ℤ) + 1)) := by
  rw [WithZero.exp_le_exp]; push_cast; omega

theorem v_lt_one_iff (x : v.adicCompletion K) :
    Valued.v x < 1 ↔ Valued.v x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hx : Valued.v x = 0
  · simp [hx]
  · rw [← WithZero.exp_log hx, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem eq_zero_of_forall_v_le (x : v.adicCompletion K)
    (h : ∀ n : ℕ, Valued.v x ≤ WithZero.exp (-((n : ℤ) + 1))) : x = 0 := by
  by_contra hx
  have hx' : Valued.v x ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]
  set L := WithZero.log (Valued.v x) with hL
  have hxL : Valued.v x = WithZero.exp L := (WithZero.exp_log hx').symm
  have := h ((-L).toNat)
  rw [hxL, WithZero.exp_le_exp] at this
  omega

theorem v_eq_one_of_sub_one {x : v.adicCompletion K} {n : ℕ}
    (hx : Valued.v (x - 1) ≤ WithZero.exp (-((n : ℤ) + 1))) : Valued.v x = 1 := by
  have : x = 1 + (x - 1) := by ring
  rw [this]
  exact Valuation.map_one_add_of_lt _ (hx.trans_lt (exp_neg_succ_lt_one n))

theorem ne_zero_of_v_eq_one {x : v.adicCompletion K} (hx : Valued.v x = 1) : x ≠ 0 := by
  intro h; rw [h, Valuation.map_zero] at hx; exact zero_ne_one hx

theorem v_inv_sub_one {x : v.adicCompletion K} {n : ℕ}
    (hx : Valued.v (x - 1) ≤ WithZero.exp (-((n : ℤ) + 1))) :
    Valued.v (x⁻¹ - 1) ≤ WithZero.exp (-((n : ℤ) + 1)) := by
  have h1 := v_eq_one_of_sub_one hx
  have hx0 := ne_zero_of_v_eq_one h1
  have : x⁻¹ - 1 = x⁻¹ * (-(x - 1)) := by field_simp; ring
  rw [this, Valuation.map_mul, Valuation.map_neg, map_inv₀, h1, inv_one, one_mul]
  exact hx

theorem isOpen_ball (m : ℤ) : IsOpen {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer K v
  have hϖ0 : ϖ ≠ 0 := uniformizer_ne_zero hϖ
  have hset : {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp m} =
      (fun x => ϖ ^ m * x) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, v_uniformizer_zpow hϖ,
      WithZero.exp_neg]
    constructor
    · intro h
      calc (WithZero.exp m)⁻¹ * Valued.v x ≤ (WithZero.exp m)⁻¹ * WithZero.exp m :=
            mul_le_mul_right h _
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · intro h
      calc Valued.v x = WithZero.exp m * ((WithZero.exp m)⁻¹ * Valued.v x) := by
            rw [← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul]
        _ ≤ WithZero.exp m * 1 := mul_le_mul_right h _
        _ = WithZero.exp m := mul_one _
  rw [hset]
  exact (Valued.isOpen_valuationSubring _).preimage (continuous_const_mul _)

theorem exists_eq_zpow_mul (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (y : v.adicCompletion K) (hy : y ≠ 0) :
    ∃ (j : ℤ) (t : v.adicCompletion K), Valued.v t = 1 ∧ y = ϖ ^ j * t ∧
      Valued.v y = WithZero.exp (-j) := by
  have hϖ0 : ϖ ≠ 0 := uniformizer_ne_zero hϖ
  have hy' : Valued.v y ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]
  set L := WithZero.log (Valued.v y) with hL
  have hyL : Valued.v y = WithZero.exp L := (WithZero.exp_log hy').symm
  refine ⟨-L, ϖ ^ L * y, ?_, ?_, ?_⟩
  · rw [Valuation.map_mul, v_uniformizer_zpow hϖ, hyL, ← WithZero.exp_add, neg_add_cancel,
      WithZero.exp_zero]
  · rw [zpow_neg, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hϖ0), one_mul]
  · rw [neg_neg, hyL]

end Valuation

section GLtwo

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => HeightOneSpectrum.adicCompletion K v
local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)

theorem mul_coe_apply (g h : G) (i j : Fin 2) :
    ((g * h : G) : Mat) i j = (g : Mat) i 0 * (h : Mat) 0 j + (g : Mat) i 1 * (h : Mat) 1 j := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

def lvl (n : ℕ) : ℤᵐ⁰ := WithZero.exp (-((n : ℤ) + 1))

theorem lvl_le_one (n : ℕ) : lvl n ≤ 1 := exp_neg_succ_le_one n

theorem lvl_lt_one (n : ℕ) : lvl n < 1 := exp_neg_succ_lt_one n

theorem lvl_succ_le (n : ℕ) : lvl (n + 1) ≤ lvl n := exp_antitone_succ n

theorem v_mul_le_lvl_left {n : ℕ} {x y : F} (hx : Valued.v x ≤ lvl n) (hy : Valued.v y ≤ 1) :
    Valued.v (x * y) ≤ lvl n := by
  rw [Valuation.map_mul]; simpa using mul_le_mul' hx hy

theorem v_mul_le_lvl_right {n : ℕ} {x y : F} (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ lvl n) :
    Valued.v (x * y) ≤ lvl n := by
  rw [Valuation.map_mul]; simpa using mul_le_mul' hx hy

theorem v_le_one_of_sub_one_le {n : ℕ} {x : F} (hx : Valued.v (x - 1) ≤ lvl n) : Valued.v x ≤ 1 := by
  have : x = (x - 1) + 1 := by ring
  rw [this]; exact v_add_le (hx.trans (lvl_le_one n)) (by simp)

structure IsCong (n : ℕ) (m : Mat) : Prop where
  h00 : Valued.v (m 0 0 - 1) ≤ lvl n
  h01 : Valued.v (m 0 1) ≤ lvl n
  h10 : Valued.v (m 1 0) ≤ lvl n
  h11 : Valued.v (m 1 1 - 1) ≤ lvl n

theorem IsCong.v00 {n : ℕ} {m : Mat} (h : IsCong n m) : Valued.v (m 0 0) = 1 := v_eq_one_of_sub_one h.h00
theorem IsCong.v11 {n : ℕ} {m : Mat} (h : IsCong n m) : Valued.v (m 1 1) = 1 := v_eq_one_of_sub_one h.h11

theorem IsCong.integral {n : ℕ} {m : Mat} (h : IsCong n m) (i j : Fin 2) : Valued.v (m i j) ≤ 1 := by
  fin_cases i <;> fin_cases j
  · exact h.v00.le
  · exact h.h01.trans (lvl_le_one n)
  · exact h.h10.trans (lvl_le_one n)
  · exact h.v11.le

theorem isCong_one (n : ℕ) : IsCong n (1 : Mat) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

theorem IsCong.mul {n : ℕ} {a b : Mat} (ha : IsCong n a) (hb : IsCong n b) : IsCong n (a * b) := by
  have e00 : (a * b) 0 0 - 1 = (a 0 0 - 1) * b 0 0 + (b 0 0 - 1) + a 0 1 * b 1 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]; ring
  have e01 : (a * b) 0 1 = a 0 0 * b 0 1 + a 0 1 * b 1 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (a * b) 1 0 = a 1 0 * b 0 0 + a 1 1 * b 1 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (a * b) 1 1 - 1 = a 1 0 * b 0 1 + ((a 1 1 - 1) * b 1 1 + (b 1 1 - 1)) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e00]
    exact v_add_le (v_add_le (v_mul_le_lvl_left ha.h00 hb.v00.le) hb.h00)
      (v_mul_le_lvl_left ha.h01 (hb.integral 1 0))
  · rw [e01]
    exact v_add_le (v_mul_le_lvl_right ha.v00.le hb.h01) (v_mul_le_lvl_left ha.h01 hb.v11.le)
  · rw [e10]
    exact v_add_le (v_mul_le_lvl_left ha.h10 hb.v00.le) (v_mul_le_lvl_right ha.v11.le hb.h10)
  · rw [e11]
    exact v_add_le (v_mul_le_lvl_left ha.h10 (hb.integral 0 1))
      (v_add_le (v_mul_le_lvl_left ha.h11 hb.v11.le) hb.h11)

theorem IsCong.v_det_sub_one {n : ℕ} {m : Mat} (h : IsCong n m) :
    Valued.v (m 0 0 * m 1 1 - m 0 1 * m 1 0 - 1) ≤ lvl n := by
  have : m 0 0 * m 1 1 - m 0 1 * m 1 0 - 1 = (m 0 0 - 1) * m 1 1 + (m 1 1 - 1) - m 0 1 * m 1 0 := by ring
  rw [this]
  exact v_sub_le (v_add_le (v_mul_le_lvl_left h.h00 h.v11.le) h.h11) (v_mul_le_lvl_left h.h01 (h.integral 1 0))

theorem IsCong.v_det {n : ℕ} {m : Mat} (h : IsCong n m) : Valued.v (m 0 0 * m 1 1 - m 0 1 * m 1 0) = 1 :=
  v_eq_one_of_sub_one h.v_det_sub_one

theorem IsCong.inv {n : ℕ} {g : G} (h : IsCong n (g : Mat)) : IsCong n ((g⁻¹ : G) : Mat) := by
  set D : F := (g : Mat) 0 0 * (g : Mat) 1 1 - (g : Mat) 0 1 * (g : Mat) 1 0 with hD
  have hvD : Valued.v D = 1 := h.v_det
  have hD0 : D ≠ 0 := ne_zero_of_v_eq_one hvD
  set B : Mat := !![(g : Mat) 1 1 / D, -(g : Mat) 0 1 / D; -(g : Mat) 1 0 / D, (g : Mat) 0 0 / D] with hB
  have hmul : (g : Mat) * B = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  have hinv : ((g⁻¹ : G) : Mat) = B := by
    rw [Matrix.coe_units_inv, Matrix.inv_eq_right_inv hmul]
  have hvdiv : ∀ x : F, Valued.v (x / D) = Valued.v x := by
    intro x; rw [map_div₀, hvD, div_one]
  rw [hinv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : B 0 0 - 1 = ((g : Mat) 1 1 - 1 - (D - 1)) / D := by
      simp only [B, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
      field_simp; ring
    rw [this, hvdiv]
    exact v_sub_le h.h11 h.v_det_sub_one
  · have : B 0 1 = -(g : Mat) 0 1 / D := by simp [B]
    rw [this, hvdiv, Valuation.map_neg]; exact h.h01
  · have : B 1 0 = -(g : Mat) 1 0 / D := by simp [B]
    rw [this, hvdiv, Valuation.map_neg]; exact h.h10
  · have : B 1 1 - 1 = ((g : Mat) 0 0 - 1 - (D - 1)) / D := by
      simp only [B, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp; ring
    rw [this, hvdiv]
    exact v_sub_le h.h00 h.v_det_sub_one

variable (K v) in

def congr (n : ℕ) : Subgroup G where
  carrier := {g | IsCong n (g : Mat)}
  one_mem' := by simpa using isCong_one n
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Matrix.GeneralLinearGroup.coe_mul] at *
    exact ha.mul hb
  inv_mem' := by
    intro g hg
    exact hg.inv

theorem mem_congr {n : ℕ} {g : G} : g ∈ congr K v n ↔ IsCong n (g : Mat) := Iff.rfl

theorem congr_antitone (n : ℕ) : congr K v (n + 1) ≤ congr K v n := by
  intro g hg
  exact ⟨hg.h00.trans (lvl_succ_le n), hg.h01.trans (lvl_succ_le n), hg.h10.trans (lvl_succ_le n),
    hg.h11.trans (lvl_succ_le n)⟩

theorem congr_antitone' {m n : ℕ} (h : m ≤ n) : congr K v n ≤ congr K v m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (congr_antitone _).trans ih

theorem isOpen_congr (n : ℕ) : IsOpen (congr K v n : Set G) := by
  have hc : ∀ i j : Fin 2, Continuous fun g : G => (g : Mat) i j := fun i j =>
    Units.continuous_val.matrix_elem i j
  have hball : IsOpen {x : F | Valued.v x ≤ lvl n} := isOpen_ball _
  have hball' : IsOpen {x : F | Valued.v (x - 1) ≤ lvl n} :=
    hball.preimage (continuous_id.sub continuous_const)
  have hset : (congr K v n : Set G) =
      ((fun g : G => (g : Mat) 0 0) ⁻¹' {x : F | Valued.v (x - 1) ≤ lvl n}) ∩
      ((fun g : G => (g : Mat) 0 1) ⁻¹' {x : F | Valued.v x ≤ lvl n}) ∩
      ((fun g : G => (g : Mat) 1 0) ⁻¹' {x : F | Valued.v x ≤ lvl n}) ∩
      ((fun g : G => (g : Mat) 1 1) ⁻¹' {x : F | Valued.v (x - 1) ≤ lvl n}) := by
    ext g
    simp only [SetLike.mem_coe, mem_congr, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨⟨⟨h.h00, h.h01⟩, h.h10⟩, h.h11⟩, fun h => ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩⟩
  rw [hset]
  exact (((hball'.preimage (hc 0 0)).inter (hball.preimage (hc 0 1))).inter
    (hball.preimage (hc 1 0))).inter (hball'.preimage (hc 1 1))

theorem rowmax_mul_le (g k : G) (hk : ∀ i j, Valued.v ((k : Mat) i j) ≤ 1) :
    max (Valued.v (((g * k : G) : Mat) 1 0)) (Valued.v (((g * k : G) : Mat) 1 1)) ≤
      max (Valued.v ((g : Mat) 1 0)) (Valued.v ((g : Mat) 1 1)) := by
  rw [mul_coe_apply, mul_coe_apply]
  refine max_le (v_add_le ?_ ?_) (v_add_le ?_ ?_)
  · rw [Valuation.map_mul]; exact (mul_le_of_le_one_right' (hk 0 0)).trans (le_max_left _ _)
  · rw [Valuation.map_mul]; exact (mul_le_of_le_one_right' (hk 1 0)).trans (le_max_right _ _)
  · rw [Valuation.map_mul]; exact (mul_le_of_le_one_right' (hk 0 1)).trans (le_max_left _ _)
  · rw [Valuation.map_mul]; exact (mul_le_of_le_one_right' (hk 1 1)).trans (le_max_right _ _)

end GLtwo

end RowCutoff47

end

theorem exists_isOpen_forall_rowCutoff_mul_eq
    (p : HeightOneSpectrum (𝓞 ℚ))
    (B : p.adicCompletion ℚ × p.adicCompletion ℚ → ℂ) (hB : IsLocallyConstant B) :
    ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        (if max (Valued.v (((g * k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0))
                (Valued.v (((g * k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) = 1
          then B ((((g * k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0),
                  (((g * k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) else 0) =
        (if max (Valued.v ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0))
                (Valued.v ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) = 1
          then B (((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0), ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) else 0) := by
  obtain ⟨ϖ, hϖ⟩ := RowCutoff47.exists_uniformizer ℚ p
  have hϖ0 : ϖ ≠ 0 := RowCutoff47.uniformizer_ne_zero hϖ
  have hr0 : 0 < ‖ϖ‖ := norm_pos_iff.mpr hϖ0
  have hr1 : ‖ϖ‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff, hϖ, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)

  set C : Set (p.adicCompletion ℚ × p.adicCompletion ℚ) := {r | Valued.v r.1 ≤ 1 ∧ Valued.v r.2 ≤ 1} with hCdef
  have hCc : IsCompact C := by
    have hO : IsCompact (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) :=
      isCompact_iff_compactSpace.mpr (show CompactSpace (p.adicCompletionIntegers ℚ) from inferInstance)
    have hCeq : C = (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) ×ˢ (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) := by
      ext r
      simp only [hCdef, Set.mem_setOf_eq, Set.mem_prod, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [hCeq]
    exact hO.prod hO

  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (c := fun a : ℂ => {z : p.adicCompletion ℚ × p.adicCompletion ℚ | B z = a})
    hCc (fun a => hB.isOpen_fiber a) (fun x _ => Set.mem_iUnion.mpr ⟨B x, rfl⟩)
  have hconst : ∀ x ∈ C, ∀ y : p.adicCompletion ℚ × p.adicCompletion ℚ, dist y x < δ → B y = B x := by
    intro x hx y hy
    obtain ⟨a, ha⟩ := hleb x hx
    have hxa : B x = a := ha (Metric.mem_ball_self hδ)
    have hya : B y = a := ha (Metric.mem_ball.mpr hy)
    rw [hya, hxa]

  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hr1
  have hsmall : ∀ d : p.adicCompletion ℚ, Valued.v d ≤ RowCutoff47.lvl n → ‖d‖ < δ := by
    intro d hd
    have hle : RowCutoff47.lvl n ≤ WithZero.exp (-(n : ℤ)) := by
      unfold RowCutoff47.lvl; rw [WithZero.exp_le_exp]; omega
    have h1 : Valued.v d ≤ Valued.v (ϖ ^ n) := by
      rw [RowCutoff47.v_uniformizer_pow hϖ]; exact hd.trans hle
    calc ‖d‖ ≤ ‖ϖ ^ n‖ := Valued.toNormedField.norm_le_iff.mpr h1
      _ = ‖ϖ‖ ^ n := norm_pow _ _
      _ < δ := hn
  refine ⟨RowCutoff47.congr ℚ p n, RowCutoff47.isOpen_congr n, fun k hk g => ?_⟩
  have hkc : RowCutoff47.IsCong n (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) := RowCutoff47.mem_congr.mp hk
  have hkic : RowCutoff47.IsCong n ((k⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :=
    RowCutoff47.mem_congr.mp ((RowCutoff47.congr ℚ p n).inv_mem hk)

  have hM : max (Valued.v (((g * k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0))
        (Valued.v (((g * k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) =
      max (Valued.v ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0)) (Valued.v ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) := by
    refine le_antisymm (RowCutoff47.rowmax_mul_le g k hkc.integral) ?_
    have h := RowCutoff47.rowmax_mul_le (g * k) k⁻¹ hkic.integral
    rwa [mul_inv_cancel_right] at h
  rw [hM]
  by_cases hone : max (Valued.v ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0)) (Valued.v ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) = 1
  · rw [if_pos hone, if_pos hone]
    have hg10 : Valued.v ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0) ≤ 1 := (le_max_left _ _).trans_eq hone
    have hg11 : Valued.v ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) ≤ 1 := (le_max_right _ _).trans_eq hone
    apply hconst ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) ⟨hg10, hg11⟩
    rw [dist_eq_norm, Prod.mk_sub_mk, Prod.norm_mk]
    refine max_lt (hsmall _ ?_) (hsmall _ ?_)
    · rw [RowCutoff47.mul_coe_apply]
      have e : (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 + (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 - (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0
          = (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 * ((k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 - 1) + (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 := by ring
      rw [e]
      exact RowCutoff47.v_add_le (RowCutoff47.v_mul_le_lvl_right hg10 hkc.h00)
        (RowCutoff47.v_mul_le_lvl_right hg11 hkc.h10)
    · rw [RowCutoff47.mul_coe_apply]
      have e : (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1 + (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 - (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1
          = (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1 + (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 * ((k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 - 1) := by ring
      rw [e]
      exact RowCutoff47.v_add_le (RowCutoff47.v_mul_le_lvl_right hg10 hkc.h01)
        (RowCutoff47.v_mul_le_lvl_right hg11 hkc.h11)
  · rw [if_neg hone, if_neg hone]

namespace ABSP

end ABSP

namespace RAT22CORE

open Filter Topology

def lf (q : ℂ) (m : ℤ) (P : Polynomial ℂ) (s : ℂ) : ℂ := q ^ ((m : ℂ) * s) * P.eval (q ^ (-s))

theorem X_zpow_eq (q : ℂ) (hq : q ≠ 0) (k : ℤ) (s : ℂ) : (q ^ (-s)) ^ k = q ^ (-(k : ℂ) * s) := by
  rw [← Complex.cpow_int_mul]; congr 1; ring

theorem q_cpow_ne_zero (q : ℂ) (hq : q ≠ 0) (z : ℂ) : q ^ z ≠ 0 := by
  rw [Complex.cpow_def]; simp [hq, Complex.exp_ne_zero]

theorem lf_mul_Xzpow (q : ℂ) (hq : q ≠ 0) (m : ℤ) (P : Polynomial ℂ) (k : ℤ) (s : ℂ) :
    (q ^ (-s)) ^ k * lf q m P s = lf q (m - k) P s := by
  simp only [lf, X_zpow_eq q hq]
  rw [← mul_assoc, ← Complex.cpow_add _ _ hq]
  congr 2; push_cast; ring

theorem lf_add (q : ℂ) (hq : q ≠ 0) (m₁ m₂ : ℤ) (P₁ P₂ : Polynomial ℂ) :
    ∃ (m : ℤ) (P : Polynomial ℂ), ∀ s : ℂ, lf q m₁ P₁ s + lf q m₂ P₂ s = lf q m P s := by
  refine ⟨max m₁ m₂, Polynomial.X ^ (max m₁ m₂ - m₁).toNat * P₁ + Polynomial.X ^ (max m₁ m₂ - m₂).toNat * P₂, fun s => ?_⟩
  simp only [lf, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, mul_add]
  have key : ∀ (mi : ℤ) (Pi : Polynomial ℂ), mi ≤ max m₁ m₂ →
      q ^ ((mi : ℂ) * s) * Pi.eval (q ^ (-s)) =
        q ^ (((max m₁ m₂ : ℤ) : ℂ) * s) * ((q ^ (-s)) ^ (max m₁ m₂ - mi).toNat * Pi.eval (q ^ (-s))) := by
    intro mi Pi hle
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), X_zpow_eq q hq, ← mul_assoc, ← Complex.cpow_add _ _ hq]
    congr 2; push_cast; ring
  rw [key m₁ P₁ (le_max_left _ _), key m₂ P₂ (le_max_right _ _)]

theorem lf_const_mul (q : ℂ) (c : ℂ) (m : ℤ) (P : Polynomial ℂ) (s : ℂ) : c * lf q m P s = lf q m (c • P) s := by
  simp only [lf, Polynomial.eval_smul, smul_eq_mul]; ring

theorem lf_poly_mul (q : ℂ) (R : Polynomial ℂ) (m : ℤ) (P : Polynomial ℂ) (s : ℂ) :
    R.eval (q ^ (-s)) * lf q m P s = lf q m (R * P) s := by
  simp only [lf, Polynomial.eval_mul]; ring

theorem lf_zero (q : ℂ) (s : ℂ) : lf q 0 0 s = 0 := by simp [lf]

theorem lf_finset_sum (q : ℂ) (hq : q ≠ 0) {ι : Type*} (t : Finset ι) (m : ι → ℤ) (P : ι → Polynomial ℂ) :
    ∃ (M : ℤ) (Q : Polynomial ℂ), ∀ s : ℂ, ∑ i ∈ t, lf q (m i) (P i) s = lf q M Q s := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, 0, fun s => by simp [lf]⟩
  | insert a t ha ih =>
      obtain ⟨M, Q, hMQ⟩ := ih
      obtain ⟨M', Q', h'⟩ := lf_add q hq (m a) M (P a) Q
      exact ⟨M', Q', fun s => by rw [Finset.sum_insert ha, hMQ s, h' s]⟩

theorem tsum_int_eq_zero_add_finset_add_tail {f : ℤ → ℂ} (a b : ℤ) (hab : a ≤ b)
    (hlo : ∀ n, n < a → f n = 0) (hf : Summable f) :
    (Summable fun n : ℤ => if b ≤ n then f n else 0) ∧
    ∑' n : ℤ, f n = ∑ n ∈ Finset.Ico a b, f n + ∑' n : ℤ, (if b ≤ n then f n else 0) := by
  set g : ℤ → ℂ := fun n => if n ∈ Finset.Ico a b then f n else 0 with hg
  set h : ℤ → ℂ := fun n => if b ≤ n then f n else 0 with hh
  have hsplit : ∀ n, f n = g n + h n := by
    intro n
    simp only [hg, hh, Finset.mem_Ico]
    by_cases h1 : n < a
    · rw [hlo n h1, if_neg (by omega), if_neg (by omega), add_zero]
    · by_cases h2 : n < b
      · rw [if_pos ⟨by omega, h2⟩, if_neg (by omega), add_zero]
      · rw [if_neg (by omega), if_pos (by omega), zero_add]
  have hs1 : Summable g := by
    apply summable_of_ne_finset_zero (s := Finset.Ico a b)
    intro n hn; simp only [hg]; rw [if_neg hn]
  have hs2 : Summable h := by
    have : h = fun n => f n - g n := by funext n; rw [hsplit n]; ring
    rw [this]; exact hf.sub hs1
  refine ⟨hs2, ?_⟩
  have hsum : HasSum f (∑' n, g n + ∑' n, h n) := by
    have := hs1.hasSum.add hs2.hasSum
    rwa [show (fun n => g n + h n) = f from funext fun n => (hsplit n).symm] at this
  rw [hsum.tsum_eq, tsum_eq_sum (s := Finset.Ico a b) (fun n hn => by simp only [hg]; rw [if_neg hn])]
  congr 1
  exact Finset.sum_congr rfl fun n hn => by simp only [hg]; rw [if_pos hn]

theorem hasSum_int_geometric_tail (r : ℂ) (hr0 : r ≠ 0) (hr : ‖r‖ < 1) (b : ℤ) (c : ℂ) :
    HasSum (fun n : ℤ => if b ≤ n then c * r ^ n else 0) (c * r ^ b * (1 - r)⁻¹) := by
  have hinj : Function.Injective fun j : ℕ => (b + j : ℤ) := fun x y h => by simpa using h
  have hgeo := hasSum_geometric_of_norm_lt_one hr
  have h2 : HasSum (fun j : ℕ => c * r ^ b * r ^ j) (c * r ^ b * (1 - r)⁻¹) := hgeo.mul_left (c * r ^ b)
  have h3 : (fun j : ℕ => c * r ^ b * r ^ j) = (fun n : ℤ => if b ≤ n then c * r ^ n else 0) ∘ fun j : ℕ => (b + j : ℤ) := by
    funext j
    simp only [Function.comp_apply]
    rw [if_pos (by omega), zpow_add₀ hr0, zpow_natCast]; ring
  rw [h3] at h2
  refine (hinj.hasSum_iff ?_).mp h2
  intro n hn
  have : ¬ b ≤ n := by
    intro hle
    exact hn ⟨(n - b).toNat, by simp only; rw [Int.toNat_of_nonneg (by omega)]; ring⟩
  rw [if_neg this]

end RAT22CORE

namespace ABSP

open Filter Topology NumberField.StandardAddChar

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)
local notation "K₀" => AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤

theorem diagOne_mul_apply_one (y : Fˣ) (k : G2) (j : Fin 2) :
    ((diagOne y * k : G2) : Matrix (Fin 2) (Fin 2) F) 1 j = (k : Matrix (Fin 2) (Fin 2) F) 1 j := by
  rw [diagOne_eq_diagUnits2, diagUnits2_mul_apply_one]; simp

theorem max_valued_row_eq_one_of_mem {k : G2} (hk : k ∈ K₀) :
    max (Valued.v ((k : Matrix (Fin 2) (Fin 2) F) 1 0)) (Valued.v ((k : Matrix (Fin 2) (Fin 2) F) 1 1)) = 1 := by
  obtain ⟨j, hj⟩ := exists_valued_row_eq_one_of_mem p hk
  refine le_antisymm (max_le (valued_apply_le_one_of_mem p hk 1 0) (valued_apply_le_one_of_mem p hk 1 1)) ?_
  have hj2 : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hj2 with rfl | rfl
  · exact hj.symm.le.trans (le_max_left _ _)
  · exact hj.symm.le.trans (le_max_right _ _)

set_option maxHeartbeats 6400000 in
theorem deepTorusLaurent
    (ϖ : (p.adicCompletion ℚ)ˣ) (hϖ : Valued.v (ϖ : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))

    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)

    (Φ₂ : p.adicCompletion ℚ × p.adicCompletion ℚ → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂)

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (E : Fin 2 → ℂ) (e : Fin 2 → ℤ)
    (hfe0 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((μ 0 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((μ 0 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((μ 0 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((μ 0 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 0 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    (hfe1 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((μ 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((μ 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((μ 1 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((μ 1 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 1 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))

    (B : p.adicCompletion ℚ × p.adicCompletion ℚ → ℂ) (hB : IsLocallyConstant B)
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ∃ (m : ℤ) (P : Polynomial ℂ) (σs : ℝ), ∀ s : ℂ, σs < s.re →
            HasSum (fun d : ℤ =>
                (Ideal.absNorm p.asIdeal : ℂ) ^ d * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(d : ℂ) * s) *
                  ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
                      Set (GL (Fin 2) (p.adicCompletion ℚ))),
                    (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                        φ (antidiagonal2 p * upperUnipotent2 p x *
                          (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero d * k)) ∂(selfDualHaarAt ℚ p)) *
                      w₂ (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero d * k) *
                      B ((k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) ∂μ₂)
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by

  letI iGL : MeasurableSpace G2 := localGLBorel ℚ p
  haveI iBGL : BorelSpace G2 := borelSpace_localGLBorel ℚ p
  letI iF : MeasurableSpace F := localBorel ℚ p
  intro μ₂ _ w₂ hw₂

  have hKNopen : IsOpen ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Subgroup G2) : Set G2) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2
  have hw₂law' : ∀ (x : F) (g : G2), w₂ (unipotent x * g) = psiLocal ℚ p x * w₂ g :=
    fun x => SpanAux.law_of_mem_span w₂base (unipotent x) (psiLocal ℚ p x) (hw₂law x) hw₂
  have hw₂sm' : ∃ U : Subgroup G2, IsOpen (U : Set G2) ∧ ∀ k ∈ U, ∀ g : G2, w₂ (g * k) = w₂ g :=
    SpanAux.exists_open_stabilizer_of_mem_span w₂base _ hKNopen hw₂K hw₂
  have hw₂central' : ∀ (z : Fˣ) (g : G2), w₂ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂ g :=
    fun z => SpanAux.law_of_mem_span w₂base _ _ (hcentral z) hw₂
  have hw₂adm' : ∀ U : Subgroup G2, IsOpen (U : Set G2) →
      ∃ B : Finset (G2 → ℂ), ∀ w' ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₂ (g * h)),
        (∀ k ∈ U, ∀ g : G2, w' (g * k) = w' g) → w' ∈ Submodule.span ℂ (B : Set (G2 → ℂ)) := by
    intro U hU
    obtain ⟨B, hB⟩ := hw₂adm U hU
    exact ⟨B, fun w' hw' hk => hB w' (SpanAux.span_le_span_of_mem w₂ w₂base hw₂ hw') hk⟩

  obtain ⟨Cw, Aw, τ, m₁, -, hKD⟩ :=
    AutomorphicForm.WhittakerModel.exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar p θ₀ w₂
      hw₂law' hw₂sm' hw₂adm' hw₂central'
  have hdiagZ : ∀ d : ℤ, (diagZ (ϖ : F) ϖ.ne_zero d : G2) = diagUnits2 (ϖ ^ d) 1 := by
    intro d; rw [diagZ_eq_diagOne, diagOne_eq_diagUnits2]
  have hlow : ∀ d : ℤ, d < -m₁ → ∀ k ∈ K₀, w₂ (diagZ (ϖ : F) ϖ.ne_zero d * k) = 0 := by
    intro d hd k hk
    rw [hdiagZ]
    refine (hKD k hk (ϖ ^ d) 1).2 ?_
    rw [inv_one, mul_one, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← WithZero.exp_zsmul, WithZero.exp_lt_exp]
    simp only [smul_eq_mul, mul_neg, mul_one]
    omega

  have hϖint : (ϖ : F) ∈ p.adicCompletionIntegers ℚ := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  set ϖO : p.adicCompletionIntegers ℚ := ⟨(ϖ : F), hϖint⟩ with hϖO
  have hϖOval : algebraMap (p.adicCompletionIntegers ℚ) F ϖO = (ϖ : F) := rfl
  have hπ : algebraMap (p.adicCompletionIntegers ℚ) F ϖO ≠ 0 := by rw [hϖOval]; exact ϖ.ne_zero
  have hϖ' : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) F ϖO) = WithZero.exp (-1 : ℤ) := by rw [hϖOval]; exact hϖ
  have hmk0 : Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) F ϖO) hπ = ϖ := Units.ext rfl
  have hq1 := one_lt_absNorm p
  have hnϖ : ‖(ϖ : F)‖ = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-1 : ℤ) := norm_eq_of_mem_shell p (n := 1) hϖ
  have hnϖ0 : 0 < ‖(ϖ : F)‖ := by rw [hnϖ]; positivity
  have hnϖ1 : ‖(ϖ : F)‖ < 1 := by rw [hnϖ, zpow_neg_one]; exact inv_lt_one_of_one_lt₀ hq1
  have hη : ‖((μ 0 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) F ϖO) hπ) : ℂˣ) : ℂ)‖ ≠
      ‖((μ 1 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) F ϖO) hπ) : ℂˣ) : ℂ)‖ := by
    rw [hmk0, hσ 0, hσ 1]
    exact ne_of_lt ((Real.rpow_lt_rpow_left_iff_of_base_lt_one hnϖ0 hnϖ1).mpr h01)
  have hmellin : ∀ w ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₂base (g * h)), ∀ i : Fin 2,
      ∃ (P : Polynomial ℂ) (m : ℤ) (σ₀ : ℝ), ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun y : Fˣ => w (diagOne y) * ((μ i y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s - 1 / 2))
          (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
        (∫ y : Fˣ, w (diagOne y) * ((μ i y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s - 1 / 2)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by
    intro w hw i
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · obtain ⟨P, -, m, -, σ₀, -, hA, hB, -, -, -⟩ := hfe0 w hw
      exact ⟨P, m, σ₀, fun s hs => ⟨hA s hs, hB s hs⟩⟩
    · obtain ⟨P, -, m, -, σ₀, -, hA, hB, -, -, -⟩ := hfe1 w hw
      exact ⟨P, m, σ₀, fun s hs => ⟨hA s hs, hB s hs⟩⟩

  set Wp : G2 → ℂ := fun g => ∫ x : F, psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)
    with hWp
  obtain ⟨Uφ, hUφ, hUφinv⟩ := LanglandsTunnell.CubicInduction.exists_isOpen_forall_mul_eq_of_mem_principalSeries2 p μ φ hφ
  have hWinv : ∀ k ∈ Uφ, ∀ g : G2, Wp (g * k) = Wp g := by
    intro k hk g
    simp only [hWp]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (g * k)) =
      psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * g)
    rw [← mul_assoc, hUφinv k hk]
  set Bc : G2 → ℂ := fun g =>
    if max (Valued.v ((g : Matrix (Fin 2) (Fin 2) F) 1 0)) (Valued.v ((g : Matrix (Fin 2) (Fin 2) F) 1 1)) = 1
      then B (((g : Matrix (Fin 2) (Fin 2) F) 1 0), ((g : Matrix (Fin 2) (Fin 2) F) 1 1)) else 0 with hBc
  obtain ⟨UB, hUB, hUBinv⟩ := exists_isOpen_forall_rowCutoff_mul_eq p B hB
  set A : G2 → ℂ := fun g => Wp g * Bc g with hA
  have hAsm : ∃ U : Subgroup G2, IsOpen (U : Set G2) ∧ ∀ k ∈ U, ∀ g : G2, A (g * k) = A g := by
    refine ⟨Uφ ⊓ UB, ?_, fun k hk g => ?_⟩
    · rw [Subgroup.coe_inf]; exact hUφ.inter hUB
    · rw [Subgroup.mem_inf] at hk
      simp only [hA]
      rw [hWinv k hk.1 g]
      congr 1
      exact hUBinv k hk.2 g
  have hBcK : ∀ k ∈ K₀, ∀ y : Fˣ, Bc (diagOne y * k) = B (((k : Matrix (Fin 2) (Fin 2) F) 1 0), ((k : Matrix (Fin 2) (Fin 2) F) 1 1)) := by
    intro k hk y
    simp only [hBc, diagOne_mul_apply_one, max_valued_row_eq_one_of_mem p hk, if_true]

  obtain ⟨c, C₀, C₁, hc, hS1⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber
      p μ hμ σ hσ h01 φ hφ
  have htail : ∃ (c : ℝ) (C₀ C₁ : G2 → ℂ), 0 < c ∧ ∀ k ∈ K₀, ∀ y : Fˣ, ‖(y : F)‖ ≤ c →
      A (diagOne y * k) = ((Real.sqrt (modulus (y : F)) : ℝ) : ℂ) * (C₁ k * ((μ 1 y : ℂˣ) : ℂ) + C₀ k * ((μ 0 y : ℂˣ) : ℂ)) := by
    refine ⟨c, fun k => C₀ k * B (((k : Matrix (Fin 2) (Fin 2) F) 1 0), ((k : Matrix (Fin 2) (Fin 2) F) 1 1)),
      fun k => C₁ k * B (((k : Matrix (Fin 2) (Fin 2) F) 1 0), ((k : Matrix (Fin 2) (Fin 2) F) 1 1)), hc, fun k hk y hy => ?_⟩
    simp only [hA]
    rw [hBcK k hk y, show Wp (diagOne y * k) = _ from hS1 k hk y hy]
    ring

  obtain ⟨N₁, hN₁⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_le_setIntegral_localLevelOne_mul_diagZ_mul_eq_zero_of_sqrt_modulus_tail_of_forall_torusZeta_polynomial
      p hπ hϖ' θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral μ hμ hη hmellin A hAsm htail μ₂ w₂ hw₂

  set I : ℤ → ℂ := fun d =>
    ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup G2) : Set G2),
      (∫ x : F, psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (diagZ (ϖ : F) ϖ.ne_zero d * k)) ∂(selfDualHaarAt ℚ p)) *
        w₂ (diagZ (ϖ : F) ϖ.ne_zero d * k) *
        B ((k : Matrix (Fin 2) (Fin 2) F) 1 0, (k : Matrix (Fin 2) (Fin 2) F) 1 1) ∂μ₂ with hI
  have hK₀m : MeasurableSet ((K₀ : Subgroup G2) : Set G2) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ top_ne_bot).2.measurableSet
  have hIlow : ∀ d, d < -m₁ → I d = 0 := by
    intro d hd
    simp only [hI]
    refine setIntegral_eq_zero_of_forall_eq_zero fun k hk => ?_
    rw [hlow d hd k hk, mul_zero, zero_mul]
  have hIhigh : ∀ d, N₁ ≤ d → I d = 0 := by
    intro d hd
    have h := hN₁ d hd
    simp only [hI]
    rw [← h]
    refine setIntegral_congr_fun hK₀m fun k hk => ?_
    have hk' : k ∈ K₀ := hk
    have e1 : (diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖO) hπ d : G2) = diagZ (ϖ : F) ϖ.ne_zero d := rfl
    simp only [hA, hBc, e1]
    rw [show ((diagZ (ϖ : F) ϖ.ne_zero d * k : G2) : Matrix (Fin 2) (Fin 2) F) 1 0 = (k : Matrix (Fin 2) (Fin 2) F) 1 0 from by
        rw [diagZ_eq_diagOne]; exact diagOne_mul_apply_one p _ k 0,
      show ((diagZ (ϖ : F) ϖ.ne_zero d * k : G2) : Matrix (Fin 2) (Fin 2) F) 1 1 = (k : Matrix (Fin 2) (Fin 2) F) 1 1 from by
        rw [diagZ_eq_diagOne]; exact diagOne_mul_apply_one p _ k 1,
      max_valued_row_eq_one_of_mem p hk', if_pos rfl]
    ring

  have hq : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq1).ne'
  obtain ⟨M, Q, hMQ⟩ := RAT22CORE.lf_finset_sum (Ideal.absNorm p.asIdeal : ℂ) hq (Finset.Ico (-m₁) N₁)
    (fun d => -d) (fun d => Polynomial.C ((Ideal.absNorm p.asIdeal : ℂ) ^ d * I d))
  refine ⟨M, Q, 0, fun s _ => ?_⟩
  have hterm : ∀ d : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ d * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(d : ℂ) * s) * I d =
      RAT22CORE.lf (Ideal.absNorm p.asIdeal : ℂ) (-d) (Polynomial.C ((Ideal.absNorm p.asIdeal : ℂ) ^ d * I d)) s := by
    intro d
    simp only [RAT22CORE.lf, Polynomial.eval_C]
    push_cast
    ring_nf
  have hfin : ∀ d ∉ Finset.Ico (-m₁) N₁,
      (Ideal.absNorm p.asIdeal : ℂ) ^ d * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(d : ℂ) * s) * I d = 0 := by
    intro d hd
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hd
    rcases hd with h | h
    · rw [hIlow d h, mul_zero]
    · rw [hIhigh d h, mul_zero]
  have hsum : HasSum (fun d : ℤ => (Ideal.absNorm p.asIdeal : ℂ) ^ d * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(d : ℂ) * s) * I d)
      (∑ d ∈ Finset.Ico (-m₁) N₁, (Ideal.absNorm p.asIdeal : ℂ) ^ d * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(d : ℂ) * s) * I d) :=
    hasSum_sum_of_ne_finset_zero hfin
  rw [Finset.sum_congr rfl (fun d _ => hterm d), hMQ s] at hsum
  simpa only [hI, RAT22CORE.lf] using hsum

end ABSP

end

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (ϖ : (p.adicCompletion ℚ)ˣ) (hϖ : Valued.v (ϖ : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))

    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)

    (Φ₂ : p.adicCompletion ℚ × p.adicCompletion ℚ → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂)

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (E : Fin 2 → ℂ) (e : Fin 2 → ℤ)
    (hfe0 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((μ 0 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((μ 0 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((μ 0 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((μ 0 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 0 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    (hfe1 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((μ 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((μ 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((μ 1 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((μ 1 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 1 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))

    (B : p.adicCompletion ℚ × p.adicCompletion ℚ → ℂ) (hB : IsLocallyConstant B)
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ∃ (m : ℤ) (P : Polynomial ℂ) (σs : ℝ), ∀ s : ℂ, σs < s.re →
            HasSum (fun d : ℤ =>
                (Ideal.absNorm p.asIdeal : ℂ) ^ d * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(d : ℂ) * s) *
                  ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
                      Set (GL (Fin 2) (p.adicCompletion ℚ))),
                    (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                        φ (antidiagonal2 p * upperUnipotent2 p x *
                          (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero d * k)) ∂(selfDualHaarAt ℚ p)) *
                      w₂ (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero d * k) *
                      B ((k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) ∂μ₂)
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) :=
  ABSP.deepTorusLaurent p ϖ hϖ μ hμ σ hσ h01 φ hφ Φ₂ hΦ₂ θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ E e
    hfe0 hfe1 B hB

end S_LanglandsTunnell_RankinSelberg_exists_hasSum_torusShells_jacquetIntegral_mul_whittaker_mul_row_eq_cpow_mul_eval_of_forall_torusZeta_polynomial_ed2
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_hasSum_torusShells_jacquetIntegral_mul_whittaker_mul_row_eq_cpow_mul_eval_of_forall_torusZeta_polynomial_ed2 (solution)
