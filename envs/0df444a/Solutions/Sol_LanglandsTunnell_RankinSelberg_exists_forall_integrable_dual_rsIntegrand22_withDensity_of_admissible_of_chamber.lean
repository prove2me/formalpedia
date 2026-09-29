-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_integrable_dual_rsIntegrand22_withDensity_of_admissible_of_chamber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/7622280d-a689-594a-bb2e-f3a8c3e4fa5f

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
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar
import Theorems.Thm_LanglandsTunnell_CubicInduction_absoluteJacquetIntegral_lt_top_and_unipotent_and_diagonal2_and_bounded_of_mem_principalSeries2
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isOpen_forall_mul_eq_of_mem_principalSeries2
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
import Theorems.Thm_AutomorphicForm_secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom
import Theorems.Thm_LanglandsTunnell_TateLocal_isSchwartzBruhat_prodFourier_and_prodFourier_prodFourier_selfDualHaarAt_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_dual_rsIntegrand22_withDensity_of_admissible_of_chamber
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

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

theorem exists_forall_apply_eq_zero_of_exp_lt₂ {Φ₂ : F × F → ℂ} (hΦc : HasCompactSupport Φ₂) :
    ∃ R : ℤ, ∀ r : F × F, (WithZero.exp R < Valued.v r.1 ∨ WithZero.exp R < Valued.v r.2) → Φ₂ r = 0 := by
  have hK : IsCompact (tsupport Φ₂) := hΦc
  obtain ⟨R₁, hR₁⟩ := exists_forall_valued_le_of_isCompact p (hK.image continuous_fst)
  obtain ⟨R₂, hR₂⟩ := exists_forall_valued_le_of_isCompact p (hK.image continuous_snd)
  refine ⟨max R₁ R₂, fun r hr => ?_⟩
  by_contra hne
  have hmem : r ∈ tsupport Φ₂ := subset_tsupport Φ₂ hne
  rcases hr with h1 | h2
  · have := hR₁ r.1 (Set.mem_image_of_mem _ hmem)
    exact absurd (this.trans (WithZero.exp_le_exp.mpr (le_max_left _ _))) (not_le.mpr h1)
  · have := hR₂ r.2 (Set.mem_image_of_mem _ hmem)
    exact absurd (this.trans (WithZero.exp_le_exp.mpr (le_max_right _ _))) (not_le.mpr h2)

theorem upperUnipotent2_eq_unipotentGL2 (x : F) : (upperUnipotent2 p x : G2) = unipotentGL2 x := Units.ext rfl

theorem continuous_transposeInvN : Continuous fun g : G2 => transposeInvN (Fin 2) g := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · show Continuous fun g : G2 => ((transposeInvN (Fin 2) g : G2) : Matrix (Fin 2) (Fin 2) F)
    simp_rw [coe_transposeInvN]
    exact Units.continuous_coe_inv.matrix_transpose
  · show Continuous fun g : G2 => (((transposeInvN (Fin 2) g)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) F)
    simp_rw [coe_inv_transposeInvN]
    exact Units.continuous_val.matrix_transpose

theorem mem_K₀_of_forall_valued_le_one {k : G2}
    (h1 : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1)
    (h2 : ∀ i j, Valued.v (((k⁻¹ : G2) : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1) : k ∈ K₀ := by
  rw [AdelicDock.mem_localLevelOne_iff]
  have aux : ∀ m : Matrix (Fin 2) (Fin 2) F, (∀ i j, Valued.v (m i j) ≤ 1) →
      AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m := by
    intro m hm
    refine ⟨fun i j => (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hm i j), ?_, ?_⟩
    · rw [NumberField.AdelicLevel.idealBound_top]; exact hm 1 0
    · rw [NumberField.AdelicLevel.idealBound_top]
      exact (Valuation.map_sub _ _ _).trans (max_le (hm 1 1) (le_of_eq (Valuation.map_one _)))
  exact ⟨aux _ h1, aux _ h2⟩

theorem w₀p_mul_w₀p (w₀p : G2) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) : w₀p * w₀p = 1 := by
  apply Units.ext
  rw [Units.val_mul, hw₀p, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_inv_w₀p (w₀p : G2) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) :
    ((w₀p⁻¹ : G2) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := by
  rw [inv_eq_of_mul_eq_one_left (w₀p_mul_w₀p p w₀p hw₀p), hw₀p]

theorem dualArg_unipotentGL2_mul (w₀p : G2) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) (x : F) (g : G2) :
    w₀p * transposeInvN (Fin 2) (unipotentGL2 x * g) = unipotentGL2 (-x) * (w₀p * transposeInvN (Fin 2) g) := by
  rw [transposeInvN_mul, ← mul_assoc, ← mul_assoc]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_transposeInvN, hw₀p, unipotentGL2_coe,
    show (((unipotentGL2 x)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) F) = !![1, -x; 0, 1] from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

theorem dualArg_diagUnits2_mul (w₀p : G2) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) (a₁ a₂ : Fˣ) (k : G2) :
    w₀p * transposeInvN (Fin 2) (diagUnits2 a₁ a₂ * k) = diagUnits2 a₂⁻¹ a₁⁻¹ * (w₀p * transposeInvN (Fin 2) k) := by
  rw [transposeInvN_mul, ← mul_assoc, ← mul_assoc]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_transposeInvN, hw₀p,
    show (((diagUnits2 a₁ a₂)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) F) = !![((a₁⁻¹ : Fˣ) : F), 0; 0, ((a₂⁻¹ : Fˣ) : F)] from rfl,
    coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

theorem dualArg_mem_K₀ (w₀p : G2) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) {k : G2} (hk : k ∈ K₀) : w₀p * transposeInvN (Fin 2) k ∈ K₀ := by
  have hv : ∀ i j, Valued.v (((w₀p * transposeInvN (Fin 2) k : G2) : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1 := by
    intro i j
    have hI : ∀ i j, Valued.v (((k : G2) : Matrix (Fin 2) (Fin 2) F)⁻¹ i j) ≤ 1 := by
      intro i j
      rw [← Matrix.coe_units_inv]
      exact valued_inv_apply_le_one_of_mem p hk i j
    rw [Units.val_mul, hw₀p, coe_transposeInvN]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, hI]
  have hvi : ∀ i j, Valued.v ((((w₀p * transposeInvN (Fin 2) k)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1 := by
    intro i j
    have hI := valued_apply_le_one_of_mem p hk
    rw [mul_inv_rev, Units.val_mul, coe_inv_transposeInvN, coe_inv_w₀p p w₀p hw₀p]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, hI]
  exact mem_K₀_of_forall_valued_le_one p hv hvi

theorem real_bound_dual {Y Z Cw CΦ CJ τ σ σ₀ σ₁ nw nΦ : ℝ} {A : ℕ}
    (hY : 0 < Y) (hZ : 0 < Z) (hCw : 0 ≤ Cw) (hCΦ : 0 ≤ CΦ) (hCJ : 0 ≤ CJ) (hnw : 0 ≤ nw) (hnΦ : 0 ≤ nΦ)
    (hw : nw ≤ Cw * (Y * Z)⁻¹ ^ τ * max 1 ((Y ^ A)⁻¹)) (hΦ : nΦ ≤ CΦ) :
    nw * nΦ * (Y * Z * Z) ^ (σ + 1) * ((Y * Z)⁻¹ ^ σ₀ * Z⁻¹ ^ σ₁ * Real.sqrt (Z⁻¹ / (Y * Z)⁻¹)) * CJ * Y⁻¹ ≤
      Cw * CΦ * CJ * (Y ^ (σ - τ - σ₀ + 1 / 2) + Y ^ (σ - τ - σ₀ + 1 / 2 - A)) *
        Z ^ (2 * σ + 2 - τ - σ₀ - σ₁) := by
  have hY' := hY.le
  have hZ' := hZ.le
  have hYZ : 0 < Y * Z := mul_pos hY hZ
  have hsq : Z⁻¹ / (Y * Z)⁻¹ = Y := by field_simp

  have hL : (Y * Z * Z) ^ (σ + 1) * ((Y * Z)⁻¹ ^ σ₀ * Z⁻¹ ^ σ₁ * Real.sqrt (Z⁻¹ / (Y * Z)⁻¹)) * Y⁻¹ =
      Y ^ (σ - σ₀ + 1 / 2) * Z ^ (2 * σ + 2 - σ₀ - σ₁) := by
    rw [hsq, Real.sqrt_eq_rpow, Real.inv_rpow hYZ.le, Real.inv_rpow hZ', ← Real.rpow_neg hYZ.le, ← Real.rpow_neg hZ',
      Real.mul_rpow (mul_nonneg hY' hZ') hZ', Real.mul_rpow hY' hZ', Real.mul_rpow hY' hZ', ← Real.rpow_neg_one Y]
    have e1 : Y ^ (σ - σ₀ + 1 / 2) = Y ^ (σ + 1) * Y ^ (-σ₀) * Y ^ (1 / 2 : ℝ) * Y ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hY, ← Real.rpow_add hY, ← Real.rpow_add hY]; congr 1; ring
    have e2 : Z ^ (2 * σ + 2 - σ₀ - σ₁) = Z ^ (σ + 1) * Z ^ (σ + 1) * Z ^ (-σ₀) * Z ^ (-σ₁) := by
      rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ]; congr 1; ring
    rw [e1, e2]; ring

  have hτ : (Y * Z)⁻¹ ^ τ = Y ^ (-τ) * Z ^ (-τ) := by
    rw [Real.inv_rpow hYZ.le, ← Real.rpow_neg hYZ.le, Real.mul_rpow hY' hZ']

  have hmax : max 1 ((Y ^ A)⁻¹) * Y ^ (σ - τ - σ₀ + 1 / 2) ≤
      Y ^ (σ - τ - σ₀ + 1 / 2) + Y ^ (σ - τ - σ₀ + 1 / 2 - A) := by
    have hp : 0 ≤ Y ^ (σ - τ - σ₀ + 1 / 2) := Real.rpow_nonneg hY' _
    have e3 : (Y ^ A)⁻¹ * Y ^ (σ - τ - σ₀ + 1 / 2) = Y ^ (σ - τ - σ₀ + 1 / 2 - A) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg hY', ← Real.rpow_add hY]; congr 1; ring
    rcases le_total 1 ((Y ^ A)⁻¹) with h | h
    · rw [max_eq_right h, e3]; linarith
    · rw [max_eq_left h, one_mul]; linarith [Real.rpow_nonneg hY' (σ - τ - σ₀ + 1 / 2 - A)]
  have hmx : 0 ≤ max 1 ((Y ^ A)⁻¹) := le_trans zero_le_one (le_max_left _ _)
  calc nw * nΦ * (Y * Z * Z) ^ (σ + 1) * ((Y * Z)⁻¹ ^ σ₀ * Z⁻¹ ^ σ₁ * Real.sqrt (Z⁻¹ / (Y * Z)⁻¹)) * CJ * Y⁻¹
      = nw * nΦ * CJ * ((Y * Z * Z) ^ (σ + 1) * ((Y * Z)⁻¹ ^ σ₀ * Z⁻¹ ^ σ₁ * Real.sqrt (Z⁻¹ / (Y * Z)⁻¹)) * Y⁻¹) := by
        ring
    _ = nw * nΦ * CJ * (Y ^ (σ - σ₀ + 1 / 2) * Z ^ (2 * σ + 2 - σ₀ - σ₁)) := by rw [hL]
    _ ≤ (Cw * (Y * Z)⁻¹ ^ τ * max 1 ((Y ^ A)⁻¹)) * CΦ * CJ * (Y ^ (σ - σ₀ + 1 / 2) * Z ^ (2 * σ + 2 - σ₀ - σ₁)) := by
        gcongr
    _ = Cw * CΦ * CJ * (max 1 ((Y ^ A)⁻¹) * (Y ^ (-τ) * Y ^ (σ - σ₀ + 1 / 2))) *
          (Z ^ (-τ) * Z ^ (2 * σ + 2 - σ₀ - σ₁)) := by
        rw [hτ]; ring
    _ = Cw * CΦ * CJ * (max 1 ((Y ^ A)⁻¹) * Y ^ (σ - τ - σ₀ + 1 / 2)) * Z ^ (2 * σ + 2 - τ - σ₀ - σ₁) := by
        rw [← Real.rpow_add hY, ← Real.rpow_add hZ]
        have ea : -τ + (σ - σ₀ + 1 / 2) = σ - τ - σ₀ + 1 / 2 := by ring
        have eb : -τ + (2 * σ + 2 - σ₀ - σ₁) = 2 * σ + 2 - τ - σ₀ - σ₁ := by ring
        rw [ea, eb]
    _ ≤ Cw * CΦ * CJ * (Y ^ (σ - τ - σ₀ + 1 / 2) + Y ^ (σ - τ - σ₀ + 1 / 2 - A)) *
          Z ^ (2 * σ + 2 - τ - σ₀ - σ₁) := by
        gcongr

set_option maxHeartbeats 3200000 in

theorem dual22

    (θ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (a : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent a * g) = NumberField.StandardAddChar.psiLocal ℚ p a * w g)
    (hwsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hwadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w' (g * k) = w' g) →
            w' ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (zc : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * g) = ((θ zc : ℂˣ) : ℂ) * w g)

    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)

    (Φ₂ : p.adicCompletion ℚ × p.adicCompletion ℚ → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂)

    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∃ σ₃ : ℝ, ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure] (s : ℂ), σ₃ < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) ∂(selfDualHaarAt ℚ p)) g * (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g) *
                    (∫ u : p.adicCompletion ℚ × p.adicCompletion ℚ, Φ₂ u *
                      NumberField.StandardAddChar.psiLocal ℚ p
                        (u.1 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 + u.2 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)
                    ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)))) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) := by

  letI iGL : MeasurableSpace G2 := localGLBorel ℚ p
  haveI iBGL : BorelSpace G2 := borelSpace_localGLBorel ℚ p
  letI iF : MeasurableSpace F := localBorel ℚ p
  haveI iBF : BorelSpace F := borelSpace_localBorel ℚ p
  haveI iBU : BorelSpace Fˣ := borelSpace_units p
  haveI iSU : SecondCountableTopology Fˣ := secondCountableTopology_units p
  obtain ⟨hSC, hLC, -, -⟩ :=
    AutomorphicForm.secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom ℚ p
  haveI := hSC
  haveI := hLC
  haveI hν : (selfDualHaarAt ℚ p).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt p
  haveI hρσ : SigmaFinite (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure Fˣ) := sigmaFinite_rho p
  haveI hρσ' : SigmaFinite (rho p) := sigmaFinite_rho p

  obtain ⟨Cw, A, τ, m₁, hCw0, hKD⟩ :=
    AutomorphicForm.WhittakerModel.exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar p θ w
      hwlaw hwsm hwadm hcentral

  have hcμ : ∀ i : Fin 2, ∃ c : ℕ, ∀ u ∈ higherUnitsAt ℚ p c, μ i u = 1 :=
    fun i => exists_forall_higherUnitsAt_eq_one p (μ i) (hμ i)
  choose cμ hcμ' using hcμ
  set ϖ : Fˣ := NumberField.AdelicLevel.uniformizerUnit ℚ p with hϖdef
  have hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ) := NumberField.AdelicLevel.valued_uniformizerUnit ℚ p
  have hq1 := one_lt_absNorm p
  have hq0 : (0 : ℝ) < ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := zero_lt_one.trans hq1
  have hnϖ : ‖(ϖ : F)‖ = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-1 : ℤ) :=
    norm_eq_of_mem_shell p (n := 1) hϖ
  have hnϖ0 : 0 < ‖(ϖ : F)‖ := by rw [hnϖ]; positivity
  have hnϖ1 : ‖(ϖ : F)‖ < 1 := by
    rw [hnϖ, zpow_neg_one]; exact inv_lt_one_of_one_lt₀ hq1
  have hdom : ‖((μ 0 ϖ : ℂˣ) : ℂ)‖ < ‖((μ 1 ϖ : ℂˣ) : ℂ)‖ := by
    rw [hσ 0, hσ 1]
    exact (Real.rpow_lt_rpow_left_iff_of_base_lt_one hnϖ0 hnϖ1).mpr h01
  obtain ⟨-, hJinv, hJtor, ⟨CJ, hCJ⟩⟩ :=
    LanglandsTunnell.CubicInduction.absoluteJacquetIntegral_lt_top_and_unipotent_and_diagonal2_and_bounded_of_mem_principalSeries2
      p μ cμ hcμ' ϖ hϖ hdom φ hφ
      (LanglandsTunnell.CubicInduction.exists_isOpen_forall_mul_eq_of_mem_principalSeries2 p μ φ hφ)
      (antidiagonal2 p) (antidiagonal2_coe p) (selfDualHaarAt ℚ p)

  set PhiHat : F × F → ℂ := fun y : F × F =>
      ∫ x : F × F, Φ₂ x * psiLocal ℚ p (x.1 * y.1 + x.2 * y.2) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))
    with hPhiHat
  have hΦh : IsLocallyConstant PhiHat ∧ HasCompactSupport PhiHat :=
    (LanglandsTunnell.TateLocal.isSchwartzBruhat_prodFourier_and_prodFourier_prodFourier_selfDualHaarAt_eq p Φ₂ hΦ₂).1
  obtain ⟨CΦ, hCΦ⟩ := hΦh.2.exists_bound_of_continuous hΦh.1.continuous
  have hCΦ0 : 0 ≤ CΦ := le_trans (norm_nonneg _) (hCΦ 0)
  obtain ⟨RΦ, hRΦ⟩ := exists_forall_apply_eq_zero_of_exp_lt₂ p hΦh.2

  obtain ⟨Uw, hUw, hUwinv⟩ := hwsm
  have hwlc : IsLocallyConstant w := isLocallyConstant_of_open_stabiliser p Uw hUw hUwinv

  have hDc : Continuous fun g : G2 => w₀p * transposeInvN (Fin 2) g :=
    continuous_const.mul (continuous_transposeInvN p)

  refine ⟨max ((A : ℝ) + τ + σ 0) ((τ + σ 0 + σ 1) / 2), ?_⟩
  intro μ₂ _ μN₂ _ s hs
  set σr : ℝ := s.re with hσr
  have hα : 0 < σr - τ - σ 0 + 1 / 2 - A := by
    have := (le_max_left _ _).trans_lt hs; linarith
  have hα' : 0 < σr - τ - σ 0 + 1 / 2 := by
    have : (0 : ℝ) ≤ A := Nat.cast_nonneg A; linarith
  have hβ : 0 < 2 * σr + 2 - τ - σ 0 - σ 1 := by
    have := (le_max_right _ _).trans_lt hs; linarith

  set Wp : G2 → ℂ := fun g => ∫ x : F, psiLocal ℚ p x *
      φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) ∂(selfDualHaarAt ℚ p) with hWp
  set X2 : G2 → ℂ := fun g =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g) *
        (∫ u : F × F, Φ₂ u *
          psiLocal ℚ p (u.1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 + u.2 * (g : Matrix (Fin 2) (Fin 2) F) 1 1)
          ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) with hX2
  set J : G2 → ENNReal := fun g => ∫⁻ y, ‖φ (antidiagonal2 p * unipotentGL2 y * g)‖ₑ ∂(selfDualHaarAt ℚ p) with hJ
  set Ms : G2 → ℂ := fun g => ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2) with hMs
  have hs' : s + 1 / 2 - 1 / 2 = s := by ring
  have hX2' : ∀ g : G2, X2 g = ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) *
      w (w₀p * transposeInvN (Fin 2) g) *
      PhiHat ((g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1) := fun g => rfl

  have hdetc : Continuous fun g : G2 => ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) := by
    have : (fun g : G2 => ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) =
        fun g : G2 => (g : Matrix (Fin 2) (Fin 2) F).det := by
      funext g; rw [Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]
    exact Units.continuous_val.matrix_det
  have hmodR : ∀ g : G2, ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) =
      ((‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ : ℝ) : ℂ) := by
    intro g
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, coe_nnnorm]
  have hmodc : Continuous fun g : G2 => ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) := by
    have : (fun g : G2 => ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ)) =
        fun g : G2 => ((‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ : ℝ) : ℂ) := funext hmodR
    rw [this]
    exact Complex.continuous_ofReal.comp (continuous_norm.comp hdetc)
  have hφc : Continuous φ := hφ.1.continuous
  have h1 : Continuous fun x : F => (upperUnipotent2 p x : G2) := by
    have : (fun x : F => (upperUnipotent2 p x : G2)) = fun x : F => (unipotentGL2 x : G2) := by
      funext x; exact upperUnipotent2_eq_unipotentGL2 p x
    rw [this]; exact continuous_unipotentGL2 p
  have hjoint : Continuous fun z : G2 × F =>
      psiLocal ℚ p z.2 * φ (antidiagonal2 p * upperUnipotent2 p z.2 * (w₀p * transposeInvN (Fin 2) z.1)) := by
    refine ((continuous_psiLocal (K := ℚ) (v := p)).comp continuous_snd).mul (hφc.comp ?_)
    exact (continuous_const.mul (h1.comp continuous_snd)).mul (hDc.comp continuous_fst)
  have hrow : Continuous fun g : G2 => ((g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1) :=
    (Units.continuous_val.matrix_elem 1 0).prodMk (Units.continuous_val.matrix_elem 1 1)
  have hX2c : Continuous X2 := by
    have : X2 = fun g : G2 => ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) *
        w (w₀p * transposeInvN (Fin 2) g) *
        PhiHat ((g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1) := funext hX2'
    rw [this]
    exact (hmodc.mul (hwlc.continuous.comp hDc)).mul (hΦh.1.continuous.comp hrow)
  have hWpm : StronglyMeasurable Wp := by
    simp only [hWp]
    exact (hjoint.stronglyMeasurable).integral_prod_right'
  have hFm : AEStronglyMeasurable (fun g : G2 => Wp g * X2 g * Ms g)
      (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := F)).range μN₂)) := by
    refine ((hWpm.mul hX2c.stronglyMeasurable).mul ?_).aestronglyMeasurable
    exact ((hmodc.measurable).pow_const _).stronglyMeasurable
  refine ⟨hFm, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]

  set h : G2 → ENNReal := fun g => J (w₀p * transposeInvN (Fin 2) g) * (‖w (w₀p * transposeInvN (Fin 2) g)‖ₑ *
      ‖PhiHat ((g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1)‖ₑ) *
      ENNReal.ofReal (‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ ^ (σr + 1)) with hh

  have hdomF : ∀ g : G2, ‖Wp g * X2 g * Ms g‖ₑ ≤ h g := by
    intro g
    have hW : ‖Wp g‖ₑ ≤ J (w₀p * transposeInvN (Fin 2) g) := by
      simp only [hWp, hJ]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun x => ?_
      rw [enorm_mul, show ‖psiLocal ℚ p x‖ₑ = 1 from by rw [← ofReal_norm_eq_enorm, norm_psiLocal, ENNReal.ofReal_one],
        one_mul, upperUnipotent2_eq_unipotentGL2]
    have hM : ‖Ms g‖ₑ = ENNReal.ofReal (‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ ^ σr) := by
      simp only [hMs]
      rw [hs', LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, coe_nnnorm, ← ofReal_norm_eq_enorm,
        Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det g).ne_zero), ← hσr]
    have hM1 : ‖((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ)‖ₑ =
        ENNReal.ofReal ‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ := by
      rw [hmodR, ← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    have hd0 : ‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (Matrix.GeneralLinearGroup.det g).ne_zero
    simp only [hh]
    rw [hX2', enorm_mul, enorm_mul, enorm_mul, enorm_mul, hM, hM1]
    calc ‖Wp g‖ₑ * (ENNReal.ofReal ‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ *
            ‖w (w₀p * transposeInvN (Fin 2) g)‖ₑ *
            ‖PhiHat ((g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1)‖ₑ) *
          ENNReal.ofReal (‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ ^ σr)
        = ‖Wp g‖ₑ * (‖w (w₀p * transposeInvN (Fin 2) g)‖ₑ *
            ‖PhiHat ((g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1)‖ₑ) *
          (ENNReal.ofReal (‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ ^ σr) *
            ENNReal.ofReal ‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖) := by ring
      _ = ‖Wp g‖ₑ * (‖w (w₀p * transposeInvN (Fin 2) g)‖ₑ *
            ‖PhiHat ((g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1)‖ₑ) *
          ENNReal.ofReal (‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ ^ (σr + 1)) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _), ← Real.rpow_add_one hd0 σr]
      _ ≤ J (w₀p * transposeInvN (Fin 2) g) * (‖w (w₀p * transposeInvN (Fin 2) g)‖ₑ *
            ‖PhiHat ((g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1)‖ₑ) *
          ENNReal.ofReal (‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ ^ (σr + 1)) := by gcongr

  have hJm : Measurable J := by
    simp only [hJ]
    have hc : Continuous fun z : G2 × F => φ (antidiagonal2 p * unipotentGL2 z.2 * z.1) :=
      hφc.comp ((continuous_const.mul ((continuous_unipotentGL2 p).comp continuous_snd)).mul continuous_fst)
    exact (hc.measurable.enorm).lintegral_prod_right'
  have hhm : Measurable h := by
    simp only [hh]
    refine ((hJm.comp hDc.measurable).mul ((hwlc.continuous.comp hDc).measurable.enorm.mul ?_)).mul ?_
    · exact (hΦh.1.continuous.comp hrow).measurable.enorm
    · exact ENNReal.measurable_ofReal.comp ((continuous_norm.comp hdetc).measurable.pow_const (σr + 1))
  have hhinv : ∀ n ∈ (unipotentGL2Hom (R := F)).range, ∀ g : G2, h (n * g) = h g := by
    rintro n ⟨x, rfl⟩ g
    have hn : (unipotentGL2Hom (R := F) x : G2) = unipotentGL2 x.toAdd := rfl
    simp only [hh]
    rw [hn]
    have e1 : J (w₀p * transposeInvN (Fin 2) (unipotentGL2 x.toAdd * g)) = J (w₀p * transposeInvN (Fin 2) g) := by
      rw [dualArg_unipotentGL2_mul p w₀p hw₀p]
      simp only [hJ]
      exact hJinv (-x.toAdd) _
    have e2 : ‖w (w₀p * transposeInvN (Fin 2) (unipotentGL2 x.toAdd * g))‖ₑ = ‖w (w₀p * transposeInvN (Fin 2) g)‖ₑ := by
      rw [dualArg_unipotentGL2_mul p w₀p hw₀p, ← unipotent_eq_unipotentGL2, hwlaw, enorm_mul,
        show ‖psiLocal ℚ p (-x.toAdd)‖ₑ = 1 from by rw [← ofReal_norm_eq_enorm, norm_psiLocal, ENNReal.ofReal_one],
        one_mul]
    have e3 : ∀ j : Fin 2, ((unipotentGL2 x.toAdd * g : G2) : Matrix (Fin 2) (Fin 2) F) 1 j = (g : Matrix (Fin 2) (Fin 2) F) 1 j := by
      intro j; rw [← unipotent_eq_unipotentGL2]; exact unipotent_mul_apply_one p _ g j
    have e4 : ((Matrix.GeneralLinearGroup.det (unipotentGL2 x.toAdd * g) : Fˣ) : F) =
        ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) := by
      rw [← unipotent_eq_unipotentGL2, det_unipotent_mul]
    rw [e1, e2, e3 0, e3 1, e4]

  obtain ⟨κ, hκ, hIW⟩ :=
    LanglandsTunnell.RankinSelberg.exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2 p μ₂ μN₂
  refine lt_of_le_of_lt (lintegral_mono fun g => hdomF g) ?_
  rw [hIW h hhm hhinv]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_

  set Cst : ENNReal := ENNReal.ofReal (Cw * CΦ * CJ) with hCst
  set B : Fˣ × Fˣ → ENNReal := fun a =>
      Cst * ((Zf p (σr - τ - σ 0 + 1 / 2) m₁ (a.1 * a.2⁻¹) + Zf p (σr - τ - σ 0 + 1 / 2 - A) m₁ (a.1 * a.2⁻¹)) *
        Zf p (2 * σr + 2 - τ - σ 0 - σ 1) RΦ a.2) with hB
  have hpt : ∀ k ∈ K₀, ∀ a₁ a₂ : Fˣ,
      h (diagUnits2 a₁ a₂ * k) * (modulus ((a₂ * a₁⁻¹ : Fˣ) : F) : ENNReal) ≤ B (a₁, a₂) := by
    intro k hk a₁ a₂

    set k' : G2 := w₀p * transposeInvN (Fin 2) k with hk'def
    have hk' : k' ∈ K₀ := dualArg_mem_K₀ p w₀p hw₀p hk
    have hba : (a₂⁻¹ * (a₁⁻¹)⁻¹ : Fˣ) = a₁ * a₂⁻¹ := by rw [inv_inv, mul_comm]
    have hY : 0 < ‖((a₁ * a₂⁻¹ : Fˣ) : F)‖ := norm_pos_iff.mpr (a₁ * a₂⁻¹).ne_zero
    have hZ : 0 < ‖(a₂ : F)‖ := norm_pos_iff.mpr a₂.ne_zero
    have ha₁ : ‖(a₁ : F)‖ = ‖((a₁ * a₂⁻¹ : Fˣ) : F)‖ * ‖(a₂ : F)‖ := by
      rw [← norm_mul, ← Units.val_mul, inv_mul_cancel_right]
    have hhval : h (diagUnits2 a₁ a₂ * k) =
        ENNReal.ofReal (‖w (diagUnits2 a₂⁻¹ a₁⁻¹ * k')‖ *
          ‖PhiHat ((a₂ : F) * (k : Matrix (Fin 2) (Fin 2) F) 1 0, (a₂ : F) * (k : Matrix (Fin 2) (Fin 2) F) 1 1)‖ *
          (‖(a₁ : F)‖ * ‖(a₂ : F)‖) ^ (σr + 1)) * J (diagUnits2 a₂⁻¹ a₁⁻¹ * k') := by
      simp only [hh]
      rw [dualArg_diagUnits2_mul p w₀p hw₀p, diagUnits2_mul_apply_one, diagUnits2_mul_apply_one, det_diagUnits2_mul,
        norm_mul, norm_mul, norm_det_eq_one_of_mem p hk, mul_one, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (norm_nonneg _)]
      ring
    have hJt : J (diagUnits2 a₂⁻¹ a₁⁻¹ * k') =
        ENNReal.ofReal (‖((μ 0 a₁⁻¹ : ℂˣ) : ℂ)‖ * ‖((μ 1 a₂⁻¹ : ℂˣ) : ℂ)‖ *
          Real.sqrt (‖((a₂⁻¹ : Fˣ) : F)‖ / ‖((a₁⁻¹ : Fˣ) : F)‖)) * J k' := by
      simp only [hJ]
      rw [diagUnits2_eq_diagonal2]
      exact hJtor a₂⁻¹ a₁⁻¹ k'
    have hJk : J k' ≤ CJ := by simp only [hJ]; exact hCJ k' hk'
    by_cases hvy : WithZero.exp m₁ < Valued.v ((a₁ * a₂⁻¹ : Fˣ) : F)
    · have h0' := (hKD k' hk' a₂⁻¹ a₁⁻¹).2
      rw [hba] at h0'
      have h0 : w (diagUnits2 a₂⁻¹ a₁⁻¹ * k') = 0 := h0' hvy
      rw [hhval, h0, norm_zero, zero_mul, zero_mul, ENNReal.ofReal_zero, zero_mul, zero_mul]
      exact bot_le
    by_cases hva : WithZero.exp RΦ < Valued.v (a₂ : F)
    · obtain ⟨j, hj⟩ := exists_valued_row_eq_one_of_mem p hk
      have h0 : PhiHat ((a₂ : F) * (k : Matrix (Fin 2) (Fin 2) F) 1 0, (a₂ : F) * (k : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
        apply hRΦ
        have hj2 : j = 0 ∨ j = 1 := by fin_cases j <;> simp
        rcases hj2 with rfl | rfl
        · left; show WithZero.exp RΦ < Valued.v ((a₂ : F) * (k : Matrix (Fin 2) (Fin 2) F) 1 0)
          rw [Valuation.map_mul, hj, mul_one]; exact hva
        · right; show WithZero.exp RΦ < Valued.v ((a₂ : F) * (k : Matrix (Fin 2) (Fin 2) F) 1 1)
          rw [Valuation.map_mul, hj, mul_one]; exact hva
      rw [hhval, h0, norm_zero, mul_zero, zero_mul, ENNReal.ofReal_zero, zero_mul, zero_mul]
      exact bot_le
    rw [not_lt] at hvy hva
    have hmodw : (modulus ((a₂ * a₁⁻¹ : Fˣ) : F) : ENNReal) = ENNReal.ofReal (‖((a₁ * a₂⁻¹ : Fˣ) : F)‖⁻¹) := by
      have hrev : (a₂ * a₁⁻¹ : Fˣ) = (a₁ * a₂⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
      rw [hrev, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm,
        Units.val_inv_eq_inv_val, norm_inv]
    have hwb := (hKD k' hk' a₂⁻¹ a₁⁻¹).1
    rw [hba, Units.val_inv_eq_inv_val, norm_inv, ha₁] at hwb
    have hBval : B (a₁, a₂) = Cst * ((ENNReal.ofReal (‖((a₁ * a₂⁻¹ : Fˣ) : F)‖ ^ (σr - τ - σ 0 + 1 / 2)) +
        ENNReal.ofReal (‖((a₁ * a₂⁻¹ : Fˣ) : F)‖ ^ (σr - τ - σ 0 + 1 / 2 - A))) *
        ENNReal.ofReal (‖(a₂ : F)‖ ^ (2 * σr + 2 - τ - σ 0 - σ 1))) := by
      show Cst * ((Zf p (σr - τ - σ 0 + 1 / 2) m₁ (a₁ * a₂⁻¹) + Zf p (σr - τ - σ 0 + 1 / 2 - A) m₁ (a₁ * a₂⁻¹)) *
        Zf p (2 * σr + 2 - τ - σ 0 - σ 1) RΦ a₂) = _
      simp only [Zf, if_pos hvy, if_pos hva]
    rw [hBval, hhval, hJt, hmodw, hCst, ← ENNReal.ofReal_add (Real.rpow_nonneg hY.le _) (Real.rpow_nonneg hY.le _),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    calc ENNReal.ofReal (‖w (diagUnits2 a₂⁻¹ a₁⁻¹ * k')‖ *
            ‖PhiHat ((a₂ : F) * (k : Matrix (Fin 2) (Fin 2) F) 1 0, (a₂ : F) * (k : Matrix (Fin 2) (Fin 2) F) 1 1)‖ *
            (‖(a₁ : F)‖ * ‖(a₂ : F)‖) ^ (σr + 1)) *
          (ENNReal.ofReal (‖((μ 0 a₁⁻¹ : ℂˣ) : ℂ)‖ * ‖((μ 1 a₂⁻¹ : ℂˣ) : ℂ)‖ *
            Real.sqrt (‖((a₂⁻¹ : Fˣ) : F)‖ / ‖((a₁⁻¹ : Fˣ) : F)‖)) * J k') *
          ENNReal.ofReal (‖((a₁ * a₂⁻¹ : Fˣ) : F)‖⁻¹)
        ≤ ENNReal.ofReal (‖w (diagUnits2 a₂⁻¹ a₁⁻¹ * k')‖ *
            ‖PhiHat ((a₂ : F) * (k : Matrix (Fin 2) (Fin 2) F) 1 0, (a₂ : F) * (k : Matrix (Fin 2) (Fin 2) F) 1 1)‖ *
            (‖(a₁ : F)‖ * ‖(a₂ : F)‖) ^ (σr + 1)) *
          (ENNReal.ofReal (‖((μ 0 a₁⁻¹ : ℂˣ) : ℂ)‖ * ‖((μ 1 a₂⁻¹ : ℂˣ) : ℂ)‖ *
            Real.sqrt (‖((a₂⁻¹ : Fˣ) : F)‖ / ‖((a₁⁻¹ : Fˣ) : F)‖)) * (CJ : ENNReal)) *
          ENNReal.ofReal (‖((a₁ * a₂⁻¹ : Fˣ) : F)‖⁻¹) := by gcongr
      _ = ENNReal.ofReal (‖w (diagUnits2 a₂⁻¹ a₁⁻¹ * k')‖ *
            ‖PhiHat ((a₂ : F) * (k : Matrix (Fin 2) (Fin 2) F) 1 0, (a₂ : F) * (k : Matrix (Fin 2) (Fin 2) F) 1 1)‖ *
            (‖((a₁ * a₂⁻¹ : Fˣ) : F)‖ * ‖(a₂ : F)‖ * ‖(a₂ : F)‖) ^ (σr + 1) *
            ((‖((a₁ * a₂⁻¹ : Fˣ) : F)‖ * ‖(a₂ : F)‖)⁻¹ ^ σ 0 * ‖(a₂ : F)‖⁻¹ ^ σ 1 *
              Real.sqrt (‖(a₂ : F)‖⁻¹ / (‖((a₁ * a₂⁻¹ : Fˣ) : F)‖ * ‖(a₂ : F)‖)⁻¹)) *
            (CJ : ℝ) * ‖((a₁ * a₂⁻¹ : Fˣ) : F)‖⁻¹) := by
          rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), hσ 0, hσ 1]
          simp only [Units.val_inv_eq_inv_val, norm_inv]
          rw [ha₁]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (Cw * CΦ * CJ *
            ((‖((a₁ * a₂⁻¹ : Fˣ) : F)‖ ^ (σr - τ - σ 0 + 1 / 2) + ‖((a₁ * a₂⁻¹ : Fˣ) : F)‖ ^ (σr - τ - σ 0 + 1 / 2 - A)) *
            ‖(a₂ : F)‖ ^ (2 * σr + 2 - τ - σ 0 - σ 1))) := by
          apply ENNReal.ofReal_le_ofReal
          refine le_trans (real_bound_dual hY hZ hCw0 hCΦ0 CJ.coe_nonneg (norm_nonneg _) (norm_nonneg _) hwb
            (hCΦ _)) (le_of_eq ?_)
          ring

  have hZm : ∀ (γ : ℝ) (M : ℤ), Measurable (Zf p γ M) := fun γ M => measurable_Zf p γ M
  have hdiv : Measurable fun a : Fˣ × Fˣ => a.1 * a.2⁻¹ := (continuous_fst.mul continuous_snd.inv).measurable
  have hBm : Measurable B := by
    show Measurable fun a : Fˣ × Fˣ =>
      Cst * ((Zf p (σr - τ - σ 0 + 1 / 2) m₁ (a.1 * a.2⁻¹) + Zf p (σr - τ - σ 0 + 1 / 2 - A) m₁ (a.1 * a.2⁻¹)) *
        Zf p (2 * σr + 2 - τ - σ 0 - σ 1) RΦ a.2)
    exact measurable_const.mul
      ((((hZm (σr - τ - σ 0 + 1 / 2) m₁).comp hdiv).add ((hZm (σr - τ - σ 0 + 1 / 2 - A) m₁).comp hdiv)).mul
        ((hZm (2 * σr + 2 - τ - σ 0 - σ 1) RΦ).comp measurable_snd))
  have hI : ∀ {γ : ℝ}, 0 < γ → ∀ (M : ℤ) (a₂ : Fˣ),
      ∫⁻ a₁, Zf p γ M (a₁ * a₂⁻¹) ∂(rho p) = ∑' n : ℤ, zg p γ M n * rho p (shell p 0) :=
    fun hγ M a₂ => lintegral_Zf_mul_inv_eq p _ M a₂
  have hBint : ∫⁻ a, B a ∂((rho p).prod (rho p)) < ⊤ := by
    rw [lintegral_prod_symm _ hBm.aemeasurable]
    have hinner : ∀ a₂ : Fˣ, ∫⁻ a₁, B (a₁, a₂) ∂(rho p) =
        Cst * (((∑' n : ℤ, zg p (σr - τ - σ 0 + 1 / 2) m₁ n * rho p (shell p 0)) +
          (∑' n : ℤ, zg p (σr - τ - σ 0 + 1 / 2 - A) m₁ n * rho p (shell p 0))) *
          Zf p (2 * σr + 2 - τ - σ 0 - σ 1) RΦ a₂) := by
      intro a₂
      have hmA : Measurable fun a₁ : Fˣ => Zf p (σr - τ - σ 0 + 1 / 2) m₁ (a₁ * a₂⁻¹) :=
        (hZm _ _).comp (measurable_id.mul_const _)
      have hmB : Measurable fun a₁ : Fˣ => Zf p (σr - τ - σ 0 + 1 / 2 - A) m₁ (a₁ * a₂⁻¹) :=
        (hZm _ _).comp (measurable_id.mul_const _)
      show ∫⁻ a₁, Cst * ((Zf p (σr - τ - σ 0 + 1 / 2) m₁ (a₁ * a₂⁻¹) + Zf p (σr - τ - σ 0 + 1 / 2 - A) m₁ (a₁ * a₂⁻¹)) *
        Zf p (2 * σr + 2 - τ - σ 0 - σ 1) RΦ a₂) ∂(rho p) = _
      rw [lintegral_const_mul _ ((hmA.fun_add hmB).mul_const _), lintegral_mul_const _ (hmA.fun_add hmB),
        lintegral_add_left hmA, hI hα' m₁ a₂, hI hα m₁ a₂]
    simp_rw [hinner]
    have hmZ : Measurable (Zf p (2 * σr + 2 - τ - σ 0 - σ 1) RΦ) := hZm _ _
    rw [lintegral_const_mul _ (hmZ.const_mul _), lintegral_const_mul _ hmZ, lintegral_Zf_eq]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ?_ (tsum_zg_lt_top p hβ RΦ))
    exact ENNReal.add_lt_top.mpr ⟨tsum_zg_lt_top p hα' m₁, tsum_zg_lt_top p hα m₁⟩

  have hK₀c : IsCompact ((K₀ : Subgroup G2) : Set G2) := (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ top_ne_bot).1
  have hμK : μ₂ ((K₀ : Subgroup G2) : Set G2) < ⊤ := hK₀c.measure_lt_top
  have hHm : Measurable fun q : G2 × (Fˣ × Fˣ) =>
      h (diagUnits2 q.2.1 q.2.2 * q.1) * (modulus ((q.2.2 * q.2.1⁻¹ : Fˣ) : F) : ENNReal) := by
    refine Measurable.mul ?_ ?_
    · have hcont : Continuous fun q : G2 × (Fˣ × Fˣ) => diagUnits2 q.2.1 q.2.2 * q.1 :=
        ((continuous_diagUnits2 p).comp continuous_snd).mul continuous_fst
      exact hhm.comp hcont.measurable
    · have : Continuous fun q : G2 × (Fˣ × Fˣ) => ((q.2.2 * q.2.1⁻¹ : Fˣ) : F) :=
        Units.continuous_val.comp ((continuous_snd.comp continuous_snd).mul (continuous_fst.comp continuous_snd).inv)
      have h2 : Continuous fun q : G2 × (Fˣ × Fˣ) => (‖((q.2.2 * q.2.1⁻¹ : Fˣ) : F)‖₊ : ENNReal) :=
        ENNReal.continuous_coe.comp (continuous_nnnorm.comp this)
      have h3 : (fun q : G2 × (Fˣ × Fˣ) => (modulus ((q.2.2 * q.2.1⁻¹ : Fˣ) : F) : ENNReal)) =
          fun q : G2 × (Fˣ × Fˣ) => (‖((q.2.2 * q.2.1⁻¹ : Fˣ) : F)‖₊ : ENNReal) := by
        funext q; rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]
      rw [h3]
      exact h2.measurable
  rw [lintegral_prod _ hHm.aemeasurable]
  calc ∫⁻ k, ∫⁻ a : Fˣ × Fˣ, h (diagUnits2 a.1 a.2 * k) *
          (modulus ((a.2 * a.1⁻¹ : Fˣ) : F) : ENNReal) ∂((rho p).prod (rho p)) ∂(μ₂.restrict ((K₀ : Subgroup G2) : Set G2))
      ≤ ∫⁻ k, (∫⁻ a, B a ∂((rho p).prod (rho p))) ∂(μ₂.restrict ((K₀ : Subgroup G2) : Set G2)) := by
        refine setLIntegral_mono measurable_const fun k hk => ?_
        exact lintegral_mono fun a => hpt k hk a.1 a.2
    _ = (∫⁻ a, B a ∂((rho p).prod (rho p))) * μ₂ ((K₀ : Subgroup G2) : Set G2) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top hBint hμK

end ABSP

end

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (θ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (a : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent a * g) = NumberField.StandardAddChar.psiLocal ℚ p a * w g)
    (hwsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hwadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w' (g * k) = w' g) →
            w' ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (zc : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * g) = ((θ zc : ℂˣ) : ℂ) * w g)

    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)

    (Φ₂ : p.adicCompletion ℚ × p.adicCompletion ℚ → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂)

    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∃ σ₃ : ℝ, ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure] (s : ℂ), σ₃ < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) ∂(selfDualHaarAt ℚ p)) g * (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g) *
                    (∫ u : p.adicCompletion ℚ × p.adicCompletion ℚ, Φ₂ u *
                      NumberField.StandardAddChar.psiLocal ℚ p
                        (u.1 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 + u.2 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)
                    ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)))) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) :=
  ABSP.dual22 p θ w hwlaw hwsm hwadm hcentral μ hμ σ hσ h01 φ hφ Φ₂ hΦ₂ w₀p hw₀p

end S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_dual_rsIntegrand22_withDensity_of_admissible_of_chamber
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_dual_rsIntegrand22_withDensity_of_admissible_of_chamber (solution)
