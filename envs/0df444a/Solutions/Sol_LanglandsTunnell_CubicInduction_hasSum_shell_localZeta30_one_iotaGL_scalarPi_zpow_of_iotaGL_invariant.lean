-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.hasSum_shell_localZeta30_one_iotaGL_scalarPi_zpow_of_iotaGL_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/908daa0e-4422-5103-928e-3b3c9c2529ac

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_sum_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_dualWhittakerFn3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isLocalZeta30ConvergentAbove_and_dual_of_isGL3PsiWhittakerFn
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_hasSum_shell_localZeta30_one_iotaGL_scalarPi_zpow_of_iotaGL_invariant
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory
open LanglandsTunnell.CubicInduction

section ZetaRationality

open NumberField.TateGlobal

namespace LocalZetaRational

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def EntriesLE (A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (e : WithZero (Multiplicative ℤ)) : Prop :=
  ∀ i j, Valued.v (A i j) ≤ e

private theorem entriesLE_mul {A B : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {x y : WithZero (Multiplicative ℤ)}
    (hA : EntriesLE v A x) (hB : EntriesLE v B y) : EntriesLE v (A * B) (x * y) := by
  intro i j
  have hterm : ∀ l, Valued.v (A i l * B l j) ≤ x * y := fun l => by
    rw [Valuation.map_mul]
    exact mul_le_mul' (hA i l) (hB l j)
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

private theorem entriesLE_add {A B : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {e : WithZero (Multiplicative ℤ)}
    (hA : EntriesLE v A e) (hB : EntriesLE v B e) : EntriesLE v (A + B) e := fun i j => by
  rw [Matrix.add_apply]
  exact le_trans (Valuation.map_add _ _ _) (max_le (hA i j) (hB i j))

private theorem entriesLE_neg {A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {e : WithZero (Multiplicative ℤ)}
    (hA : EntriesLE v A e) : EntriesLE v (-A) e := fun i j => by
  rw [Matrix.neg_apply, Valuation.map_neg]
  exact hA i j

private theorem entriesLE_mono {A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {e e' : WithZero (Multiplicative ℤ)}
    (h : e ≤ e') (hA : EntriesLE v A e) : EntriesLE v A e' := fun i j => (hA i j).trans h

private theorem entriesLE_one_of_mem {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    EntriesLE v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 ∧
      EntriesLE v ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 :=
  (mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hk

private def principalCongruence3 (m : ℕ) : Subgroup (LocalGL3 v) where
  carrier := {k | k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧
    EntriesLE v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) (WithZero.exp (-(m : ℤ)))}
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    intro i j
    rw [Units.val_one, sub_self, Matrix.zero_apply, Valuation.map_zero]
    exact zero_le'
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have hid : ((a * b : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
        (a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
          ((b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) +
        ((a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) := by
      rw [Units.val_mul, mul_sub, mul_one, sub_add_sub_cancel]
    rw [hid]
    refine entriesLE_add v ?_ ha'
    simpa only [one_mul] using entriesLE_mul v (entriesLE_one_of_mem v ha).1 hb'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have hid : ((a⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
        ((a⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
          (-((a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1)) := by
      rw [neg_sub, mul_sub, mul_one, Units.inv_mul]
    rw [hid]
    simpa only [one_mul] using entriesLE_mul v (entriesLE_one_of_mem v ha).2 (entriesLE_neg v ha')

private theorem mem_principalCongruence3_iff {m : ℕ} {k : LocalGL3 v} :
    k ∈ principalCongruence3 v m ↔ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧
      EntriesLE v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) (WithZero.exp (-(m : ℤ))) :=
  Iff.rfl

private theorem principalCongruence3_le_localMaximalCompact3 (m : ℕ) :
    principalCongruence3 v m ≤ localMaximalCompact3 (𝓞 ℚ) ℚ v := fun _ hk => hk.1

private theorem principalCongruence3_antitone {m m' : ℕ} (h : m ≤ m') :
    principalCongruence3 v m' ≤ principalCongruence3 v m := fun _ hk =>
  ⟨hk.1, entriesLE_mono v (WithZero.exp_le_exp.mpr (by omega)) hk.2⟩

private theorem conj_mem_principalCongruence3 {m : ℕ} {k g : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (hg : g ∈ principalCongruence3 v m) : k * g * k⁻¹ ∈ principalCongruence3 v m := by
  refine ⟨mul_mem (mul_mem hk hg.1) (inv_mem hk), ?_⟩
  have hid : ((k * g * k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
      (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
        ((g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) *
        ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv]
  rw [hid]
  have h1 := entriesLE_mul v (entriesLE_one_of_mem v hk).1 hg.2
  have h2 := entriesLE_mul v h1 (entriesLE_one_of_mem v hk).2
  simpa only [one_mul, mul_one] using h2

private theorem isOpen_setOf_forall_entry_mem {S : Set (v.adicCompletion ℚ)} (hS : IsOpen S) :
    IsOpen {A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) | ∀ i j, A i j ∈ S} := by
  have h : {A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) | ∀ i j, A i j ∈ S} =
      ⋂ i, ⋂ j, (fun A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) => A i j) ⁻¹' S := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hS.preimage (continuous_id.matrix_elem i j)

private theorem exists_setOf_forall_entry_sub_le_subset_of_isOpen
    {A : Set (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))} (hA : IsOpen A)
    {C : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} (hC : C ∈ A) :
    ∃ j : ℕ, {X : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) |
      ∀ i l, Valued.v (X i l - C i l) ≤ WithZero.exp (-(j : ℤ))} ⊆ A := by
  obtain ⟨u, hu, huA⟩ := (isOpen_pi_iff'.mp hA) C hC
  have hrow : ∀ i, ∃ w : Fin 3 → Set (v.adicCompletion ℚ),
      (∀ l, IsOpen (w l) ∧ C i l ∈ w l) ∧ Set.univ.pi w ⊆ u i :=
    fun i => (isOpen_pi_iff'.mp (hu i).1) (C i) (hu i).2
  choose w hw hwu using hrow
  have hball : ∀ i l, ∃ j : ℤ,
      {x : v.adicCompletion ℚ | Valued.v (x - C i l) ≤ WithZero.exp (-j)} ⊆ w i l :=
    fun i l => exists_setOf_valued_sub_le_subset_of_isOpen v (hw i l).1 (hw i l).2
  choose jj hjj using hball
  refine ⟨Finset.univ.sup fun p : Fin 3 × Fin 3 => (jj p.1 p.2).toNat, fun X hX => ?_⟩
  refine huA (Set.mem_univ_pi.mpr fun i => hwu i (Set.mem_univ_pi.mpr fun l => hjj i l ?_))
  have h1 : jj i l ≤ ((jj i l).toNat : ℤ) := Int.self_le_toNat _
  have h2 : (jj i l).toNat ≤ Finset.univ.sup fun p : Fin 3 × Fin 3 => (jj p.1 p.2).toNat :=
    Finset.le_sup (f := fun p : Fin 3 × Fin 3 => (jj p.1 p.2).toNat) (Finset.mem_univ (i, l))
  exact (hX i l).trans (WithZero.exp_le_exp.mpr (by omega))

private theorem isOpen_principalCongruence3 (m : ℕ) : IsOpen (principalCongruence3 v m : Set (LocalGL3 v)) := by
  have hball1 : IsOpen {x : v.adicCompletion ℚ | Valued.v x ≤ 1} := by
    simpa only [sub_zero, neg_zero, WithZero.exp_zero] using (isClopen_setOf_valued_sub_le v 0 0).isOpen
  have hballm : IsOpen {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-(m : ℤ))} := by
    simpa only [sub_zero] using (isClopen_setOf_valued_sub_le v 0 (m : ℤ)).isOpen
  have h1 : IsOpen ((fun k : LocalGL3 v => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) ⁻¹'
      {A | ∀ i j, A i j ∈ {x : v.adicCompletion ℚ | Valued.v x ≤ 1}}) :=
    (isOpen_setOf_forall_entry_mem v hball1).preimage Units.continuous_val
  have h2 : IsOpen ((fun k : LocalGL3 v => ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) ⁻¹'
      {A | ∀ i j, A i j ∈ {x : v.adicCompletion ℚ | Valued.v x ≤ 1}}) :=
    (isOpen_setOf_forall_entry_mem v hball1).preimage Units.continuous_coe_inv
  have h3 : IsOpen ((fun k : LocalGL3 v => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) ⁻¹'
      {A | ∀ i j, A i j ∈ {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-(m : ℤ))}}) :=
    (isOpen_setOf_forall_entry_mem v hballm).preimage (Units.continuous_val.sub continuous_const)
  convert (h1.inter h2).inter h3 using 1
  rfl

private
theorem exists_principalCongruence3_le_of_isOpen (U : Subgroup (LocalGL3 v)) (hU : IsOpen (U : Set (LocalGL3 v))) :
    ∃ m : ℕ, principalCongruence3 v m ≤ U := by
  have hmem : (U : Set (LocalGL3 v)) ∈ nhds (1 : LocalGL3 v) := hU.mem_nhds (one_mem U)
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hmem
  obtain ⟨T, hT, hTU⟩ := hmem
  rw [Units.embedProduct_apply, inv_one, Units.val_one, mem_nhds_prod_iff] at hT
  obtain ⟨A, hA, B, hB, hABT⟩ := hT
  obtain ⟨A₀, hA₀A, hA₀, h1A₀⟩ := mem_nhds_iff.mp hA
  have hB' : (MulOpposite.op : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) → _) ⁻¹' B ∈
      nhds (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hB
  obtain ⟨B₀, hB₀B, hB₀, h1B₀⟩ := mem_nhds_iff.mp hB'
  obtain ⟨j₁, hj₁⟩ := exists_setOf_forall_entry_sub_le_subset_of_isOpen v hA₀ h1A₀
  obtain ⟨j₂, hj₂⟩ := exists_setOf_forall_entry_sub_le_subset_of_isOpen v hB₀ h1B₀
  refine ⟨max j₁ j₂, fun k hk => ?_⟩
  have hball : ∀ {g : LocalGL3 v}, g ∈ principalCongruence3 v (max j₁ j₂) → ∀ j : ℕ, j ≤ max j₁ j₂ →
      (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) ∈
        {X : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) | ∀ i l,
          Valued.v (X i l - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i l) ≤ WithZero.exp (-(j : ℤ))} := by
    intro g hg j hj i l
    have h := hg.2 i l
    rw [Matrix.sub_apply] at h
    exact h.trans (WithZero.exp_le_exp.mpr (by omega))
  apply hTU
  show Units.embedProduct _ k ∈ T
  rw [Units.embedProduct_apply]
  exact hABT ⟨hA₀A (hj₁ (hball hk j₁ (le_max_left _ _))),
    hB₀B (hj₂ (hball (inv_mem hk) j₂ (le_max_right _ _)))⟩

private theorem exists_level_of_smooth {W : LocalGL3 v → ℂ}
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ u ∈ Uv, ∀ g, W (g * u) = W g) :
    ∃ m : ℕ, ∀ u ∈ principalCongruence3 v m, ∀ g, W (g * u) = W g := by
  obtain ⟨Uv, hUo, hUW⟩ := hsm
  obtain ⟨m, hm⟩ := exists_principalCongruence3_le_of_isOpen v Uv hUo
  exact ⟨m, fun u hu g => hUW u (hm hu) g⟩

private
theorem level_of_translate {W : LocalGL3 v → ℂ} {m : ℕ} (hW : ∀ u ∈ principalCongruence3 v m, ∀ g, W (g * u) = W g)
    {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    ∀ u ∈ principalCongruence3 v m, ∀ g, W (g * u * k) = W (g * k) := by
  intro u hu g
  have hconj := conj_mem_principalCongruence3 v (inv_mem hk) hu
  rw [inv_inv] at hconj
  have h := hW _ hconj (g * k)
  simpa only [← mul_assoc, mul_inv_cancel_right] using h

section MeasureInvariance

open Set Filter Topology IsDedekindDomain.HeightOneSpectrum
open scoped NNReal ENNReal Pointwise

section Invariance

variable {K : Type*} [GroupWithZero K] [TopologicalSpace K] [ContinuousMul K] [T1Space K]
  [MeasurableSpace K] [BorelSpace K]

private theorem measurableSet_preimage_of_mul_invariant_nhds {X : Type*} (f : K → X) (U : Set K) (hU : U ∈ 𝓝 (1 : K))
    (hf : ∀ x : K, ∀ u ∈ U, f (x * u) = f x) (S : Set X) : MeasurableSet (f ⁻¹' S) := by
  have hopen : IsOpen (f ⁻¹' S \ {0}) := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hxS, hx0⟩
    have hx : x ≠ 0 := hx0
    have hmem : (Units.mk0 x hx) • U ∈ 𝓝 x := by
      have := smul_mem_nhds_smul (Units.mk0 x hx) hU
      rwa [Units.smul_def, Units.val_mk0, smul_eq_mul, mul_one] at this
    refine Filter.mem_of_superset (Filter.inter_mem hmem (isOpen_compl_singleton.mem_nhds hx0)) ?_
    rintro y ⟨⟨u, huU, rfl⟩, hy0⟩
    refine ⟨?_, hy0⟩
    show f ((Units.mk0 x hx) • u) ∈ S
    rw [Units.smul_def, Units.val_mk0, smul_eq_mul, hf x u huU]
    exact hxS
  rw [← diff_union_inter (f ⁻¹' S) {0}]
  exact hopen.measurableSet.union ((subsingleton_singleton.anti inter_subset_right).measurableSet)

end Invariance

section ShellHaar

private def valShell (n : ℤ) : Set (v.adicCompletion ℚ) := {x | Valued.v x = WithZero.exp (-n)}

private theorem mem_valShell {n : ℤ} {x : v.adicCompletion ℚ} : x ∈ valShell v n ↔ Valued.v x = WithZero.exp (-n) :=
  Iff.rfl

private theorem ne_zero_of_mem_valShell {n : ℤ} {x : v.adicCompletion ℚ} (hx : x ∈ valShell v n) : x ≠ 0 := by
  rintro rfl
  exact WithZero.exp_ne_zero ((map_zero _).symm.trans hx).symm

private theorem ball_one_mem_nhds : {y : v.adicCompletion ℚ | Valued.v (y - 1) < 1} ∈ 𝓝 (1 : v.adicCompletion ℚ) := by
  refine Valued.mem_nhds.mpr ⟨1, fun z hz => ?_⟩
  have hz' : Valued.v.restrict (z - 1) < 1 := by
    rw [← Units.val_one]; exact hz
  exact (Valuation.restrict_lt_one_iff _).mp hz'

private theorem valued_eq_one_of_mem_ball {y : v.adicCompletion ℚ}
    (hy : y ∈ {y : v.adicCompletion ℚ | Valued.v (y - 1) < 1}) : Valued.v y = 1 := by
  have : y = 1 + (y - 1) := by ring
  rw [this]
  exact Valuation.map_one_add_of_lt _ hy

private theorem measurableSet_valShell (n : ℤ) :
    letI := localBorel ℚ v
    MeasurableSet (valShell v n) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have : valShell v n = Valued.v ⁻¹' {WithZero.exp (-n)} := rfl
  rw [this]
  refine measurableSet_preimage_of_mul_invariant_nhds (Valued.v : v.adicCompletion ℚ → WithZero (Multiplicative ℤ)) _
    (ball_one_mem_nhds v) (fun x u hu => ?_) _
  rw [map_mul, valued_eq_one_of_mem_ball v hu, mul_one]

private def valBall : Set (v.adicCompletion ℚ) := {x | Valued.v x ≤ 1}

private theorem valBall_eq_integers :
    valBall v = (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  ext x
  simp [valBall, mem_adicCompletionIntegers]

private
theorem smul_valBall_of_valued_eq_one (u : (v.adicCompletion ℚ)ˣ) (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    u • valBall v = valBall v := by
  ext y
  rw [mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul]
  show Valued.v (((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y) ≤ 1 ↔ Valued.v y ≤ 1
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one, one_mul]

private theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ v
    (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  unfold selfDualHaarAt
  exact Measure.IsAddHaarMeasure.nnreal_smul _
    (NNReal.rpow_pos (pos_iff_ne_zero.2 (NumberField.HeightOneSpectrum.absNorm_ne_zero v))).ne'

private theorem regular_selfDualHaarAt :
    letI := localBorel ℚ v
    (selfDualHaarAt ℚ v).Regular := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  unfold selfDualHaarAt
  rw [ENNReal.smul_def]
  exact Measure.Regular.smul ENNReal.coe_ne_top

private theorem selfDualHaarAt_valBall_ne_zero : selfDualHaarAt ℚ v (valBall v) ≠ 0 := by
  rw [valBall_eq_integers, ← coe_integersPositiveCompacts]
  unfold selfDualHaarAt
  simp only [Measure.smul_apply, Measure.addHaarMeasure_self, ENNReal.smul_def, smul_eq_mul, mul_one, ne_eq,
    ENNReal.coe_eq_zero]
  exact (NNReal.rpow_pos (pos_iff_ne_zero.2 (NumberField.HeightOneSpectrum.absNorm_ne_zero v))).ne'

private theorem selfDualHaarAt_valBall_ne_top : selfDualHaarAt ℚ v (valBall v) ≠ ⊤ := by
  rw [valBall_eq_integers, ← coe_integersPositiveCompacts]
  unfold selfDualHaarAt
  simp only [Measure.smul_apply, Measure.addHaarMeasure_self, ENNReal.smul_def, smul_eq_mul, mul_one, ne_eq,
    ENNReal.coe_ne_top, not_false_eq_true]

private theorem distribHaarChar_eq_one (u : (v.adicCompletion ℚ)ˣ) (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    distribHaarChar (v.adicCompletion ℚ) u = 1 := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := isAddHaarMeasure_selfDualHaarAt v
  haveI := regular_selfDualHaarAt v
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := selfDualHaarAt ℚ v) (s := valBall v)
    (selfDualHaarAt_valBall_ne_zero v) (selfDualHaarAt_valBall_ne_top v) ?_
  rw [ENNReal.coe_one, one_mul, smul_valBall_of_valued_eq_one v u hu]

private theorem map_mul_left_selfDualHaarAt (u : v.adicCompletion ℚ) (hu : Valued.v u = 1) :
    letI := localBorel ℚ v
    Measure.map (fun x => u * x) (selfDualHaarAt ℚ v) = selfDualHaarAt ℚ v := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := isAddHaarMeasure_selfDualHaarAt v
  haveI := regular_selfDualHaarAt v
  have hu0 : u ≠ 0 := fun h => zero_ne_one (by rw [← hu, h, map_zero])
  have hU1 : distribHaarChar (v.adicCompletion ℚ) (Units.mk0 u hu0)⁻¹ = 1 := by
    rw [map_inv, distribHaarChar_eq_one v (Units.mk0 u hu0) (by rw [Units.val_mk0]; exact hu), inv_one]
  ext s hs
  rw [Measure.map_apply (measurable_const_mul u) hs]
  have hpre : (fun x => u * x) ⁻¹' s = (Units.mk0 u hu0)⁻¹ • s := by
    ext x
    rw [mem_preimage, mem_inv_smul_set_iff, Units.smul_def, Units.val_mk0, smul_eq_mul]
  rw [hpre, ← distribHaarChar_mul (μ := selfDualHaarAt ℚ v) (Units.mk0 u hu0)⁻¹ s, hU1, ENNReal.coe_one, one_mul]

private theorem setIntegral_valShell_comp_mul (u : v.adicCompletion ℚ) (hu : Valued.v u = 1) (n : ℤ)
    (φ : v.adicCompletion ℚ → ℂ) :
    letI := localBorel ℚ v
    ∫ x in valShell v n, φ (u * x) ∂selfDualHaarAt ℚ v = ∫ x in valShell v n, φ x ∂selfDualHaarAt ℚ v := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hu0 : u ≠ 0 := fun h => zero_ne_one (by rw [← hu, h, map_zero])
  have hpre : (MeasurableEquiv.mulLeft₀ u hu0) ⁻¹' valShell v n = valShell v n := by
    ext x
    show u * x ∈ valShell v n ↔ x ∈ valShell v n
    rw [mem_valShell, mem_valShell, map_mul, hu, one_mul]
  have hmap : (selfDualHaarAt ℚ v).map (MeasurableEquiv.mulLeft₀ u hu0) = selfDualHaarAt ℚ v := by
    rw [MeasurableEquiv.coe_mulLeft₀]; exact map_mul_left_selfDualHaarAt v u hu
  calc ∫ x in valShell v n, φ (u * x) ∂selfDualHaarAt ℚ v
      = ∫ x, φ (MeasurableEquiv.mulLeft₀ u hu0 x)
          ∂(selfDualHaarAt ℚ v).restrict (MeasurableEquiv.mulLeft₀ u hu0 ⁻¹' valShell v n) := by
        simp_rw [hpre, MeasurableEquiv.coe_mulLeft₀]
    _ = ∫ y, φ y ∂((selfDualHaarAt ℚ v).restrict (MeasurableEquiv.mulLeft₀ u hu0 ⁻¹' valShell v n)).map
          (MeasurableEquiv.mulLeft₀ u hu0) := (integral_map_equiv _ φ).symm
    _ = ∫ y in valShell v n, φ y ∂selfDualHaarAt ℚ v := by
        rw [← MeasurableEquiv.restrict_map, hmap]

private theorem setIntegral_valShell_eq_zero_of_comp_mul (u : v.adicCompletion ℚ) (hu : Valued.v u = 1) (n : ℤ)
    (φ : v.adicCompletion ℚ → ℂ) (c : ℂ) (hc : c ≠ 1) (hφ : ∀ x ∈ valShell v n, φ (u * x) = c * φ x) :
    letI := localBorel ℚ v
    ∫ x in valShell v n, φ x ∂selfDualHaarAt ℚ v = 0 := by
  letI := localBorel ℚ v
  have h := setIntegral_valShell_comp_mul v u hu n φ
  rw [setIntegral_congr_fun (measurableSet_valShell v n) (fun x hx => hφ x hx), integral_const_mul] at h
  have h' : (c - 1) * ∫ x in valShell v n, φ x ∂selfDualHaarAt ℚ v = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hc)

end ShellHaar

end MeasureInvariance

section TorusLine

open Set

private noncomputable def torusFn (G : (v.adicCompletion ℚ)ˣ → ℂ) (x : v.adicCompletion ℚ) : ℂ := by
  classical exact if hx : x = 0 then 0 else G (Units.mk0 x hx)

private theorem torusFn_of_ne_zero (G : (v.adicCompletion ℚ)ˣ → ℂ) {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    torusFn v G x = G (Units.mk0 x hx) := by
  rw [torusFn, dif_neg hx]

private theorem coe_iotaGL_diagUnitGL2 (u : (v.adicCompletion ℚ)ˣ) :
    ((iotaGL (diagUnitGL2 u) : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![(u : v.adicCompletion ℚ), 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, diagUnitGL2]

private theorem iotaGL_diagUnitGL2_mul_of_diagonal (u : (v.adicCompletion ℚ)ˣ) (t : LocalGL3 v)
    (d : Fin 3 → v.adicCompletion ℚ) (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) :
    iotaGL (diagUnitGL2 u) * t = t * iotaGL (diagUnitGL2 u) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_iotaGL_diagUnitGL2, ht, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1; funext i; exact mul_comm _ _

private theorem iotaGL_diagUnitGL2_mem_localMaximalCompact3 (u : (v.adicCompletion ℚ)ˣ)
    (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    iotaGL (diagUnitGL2 u) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have hinv : (iotaGL (diagUnitGL2 u))⁻¹ = (iotaGL (diagUnitGL2 u⁻¹) : LocalGL3 v) := by
    rw [← diagHom_apply, ← diagHom_apply, map_inv, map_inv]
  rw [mem_localMaximalCompact3_iff, hinv, coe_iotaGL_diagUnitGL2, coe_iotaGL_diagUnitGL2]
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hu]

private theorem torus_mul_upperUnipotent3 (u : (v.adicCompletion ℚ)ˣ) (x y z : v.adicCompletion ℚ) :
    iotaGL (diagUnitGL2 u) * upperUnipotent3 x y z =
      upperUnipotent3 ((u : v.adicCompletion ℚ) * x) y ((u : v.adicCompletion ℚ) * z) * iotaGL (diagUnitGL2 u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, upperUnipotent3, diagUnitGL2, Matrix.mul_apply, Fin.sum_univ_three]

private theorem iotaGL_diagUnitGL2_mul (u a : (v.adicCompletion ℚ)ˣ) :
    (iotaGL (diagUnitGL2 (u * a)) : LocalGL3 v) = iotaGL (diagUnitGL2 u) * iotaGL (diagUnitGL2 a) := by
  rw [← diagHom_apply, ← diagHom_apply, ← diagHom_apply, map_mul, map_mul]

private theorem diagonal_mul_u12 (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) (y : v.adicCompletion ℚ) :
    t * upperUnipotent3 (d 1 * y) 0 0 = upperUnipotent3 (d 0 * y) 0 0 * t := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ht]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Matrix.mul_apply, Matrix.diagonal]
  ring

private
theorem u12_inv (x : v.adicCompletion ℚ) : (upperUnipotent3 x 0 0 : LocalGL3 v)⁻¹ = upperUnipotent3 (-x) 0 0 := by
  apply Units.ext
  show (upperUnipotent3 x 0 0 : LocalGL3 v).inv =
    ((upperUnipotent3 (-x) 0 0 : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3]

private
theorem entriesLE_u12_sub_one {x : v.adicCompletion ℚ} {e : WithZero (Multiplicative ℤ)} (hx : Valued.v x ≤ e) :
    EntriesLE v (((upperUnipotent3 x 0 0 : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) e := by
  intro i j
  rw [Matrix.sub_apply]
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, hx]

private
theorem u12_mem_principalCongruence3 {m : ℕ} {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ WithZero.exp (-(m : ℤ))) :
    upperUnipotent3 x 0 0 ∈ principalCongruence3 v m := by
  have hx1 : Valued.v x ≤ 1 :=
    hx.trans ((WithZero.exp_le_exp.mpr (show (-(m : ℤ)) ≤ 0 by omega)).trans_eq WithZero.exp_zero)
  refine ⟨(mem_localMaximalCompact3_iff (R := 𝓞 ℚ) (K := ℚ) (v := v)).mpr ⟨fun i j => ?_, fun i j => ?_⟩,
    entriesLE_u12_sub_one v hx⟩
  · fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, hx1]
  · rw [u12_inv]
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, hx1]

private theorem entriesLE_diagUnit_sub_one (u : (v.adicCompletion ℚ)ˣ) {e : WithZero (Multiplicative ℤ)}
    (huM : Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ e) :
    EntriesLE v (((iotaGL (diagUnitGL2 u) : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) e := by
  intro i j
  rw [Matrix.sub_apply, coe_iotaGL_diagUnitGL2]
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, huM]

private theorem iotaGL_diagUnitGL2_mem_principalCongruence3 (u : (v.adicCompletion ℚ)ˣ) (M : ℕ)
    (hu1 : Valued.v (u : v.adicCompletion ℚ) = 1)
    (huM : Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(M : ℤ))) :
    iotaGL (diagUnitGL2 u) ∈ principalCongruence3 v M :=
  ⟨iotaGL_diagUnitGL2_mem_localMaximalCompact3 v u hu1, entriesLE_diagUnit_sub_one v u huM⟩

private theorem whittaker_torus_eq_zero_of_large {ψ : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) {m : ℕ} (hWm : ∀ u ∈ principalCongruence3 v m, ∀ h, W (h * u) = W h)
    {t : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) (hd0 : d 0 ≠ 0)
    {k₀ : LocalGL3 v} (hk₀ : k₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) {y₀ : v.adicCompletion ℚ} (hy₀ : ψ y₀ ≠ 1)
    (a : (v.adicCompletion ℚ)ˣ)
    (ha : Valued.v (d 1) * Valued.v y₀ ≤
      WithZero.exp (-(m : ℤ)) * (Valued.v (a : v.adicCompletion ℚ) * Valued.v (d 0))) :
    W (iotaGL (diagUnitGL2 a) * t * k₀) = 0 := by
  have had0 : (a : v.adicCompletion ℚ) * d 0 ≠ 0 := mul_ne_zero a.ne_zero hd0
  have hsmall : Valued.v (d 1 * ((((a : v.adicCompletion ℚ) * d 0)⁻¹) * y₀)) ≤ WithZero.exp (-(m : ℤ)) := by
    calc Valued.v (d 1 * ((((a : v.adicCompletion ℚ) * d 0)⁻¹) * y₀))
        = Valued.v (d 1) * Valued.v y₀ * (Valued.v ((a : v.adicCompletion ℚ) * d 0))⁻¹ := by
          rw [map_mul, map_mul, map_inv₀, mul_comm ((Valued.v ((a : v.adicCompletion ℚ) * d 0))⁻¹) (Valued.v y₀),
            mul_assoc]
      _ ≤ WithZero.exp (-(m : ℤ)) * Valued.v ((a : v.adicCompletion ℚ) * d 0) *
            (Valued.v ((a : v.adicCompletion ℚ) * d 0))⁻¹ :=
          mul_le_mul_left (by rwa [map_mul]) _
      _ = WithZero.exp (-(m : ℤ)) := by
          rw [mul_assoc, mul_inv_cancel₀ ((Valuation.ne_zero_iff _).mpr had0), mul_one]
  have hfix : W (iotaGL (diagUnitGL2 a) * t * k₀) =
      W (iotaGL (diagUnitGL2 a) * t * upperUnipotent3 (d 1 * ((((a : v.adicCompletion ℚ) * d 0)⁻¹) * y₀)) 0 0 *
        k₀) :=
    (level_of_translate v hWm hk₀ _ (u12_mem_principalCongruence3 v hsmall) _).symm
  have hmove : iotaGL (diagUnitGL2 a) * t * upperUnipotent3 (d 1 * ((((a : v.adicCompletion ℚ) * d 0)⁻¹) * y₀)) 0 0 =
      upperUnipotent3 ((a : v.adicCompletion ℚ) * (d 0 * ((((a : v.adicCompletion ℚ) * d 0)⁻¹) * y₀))) 0
        ((a : v.adicCompletion ℚ) * 0) * (iotaGL (diagUnitGL2 a) * t) := by
    rw [mul_assoc, diagonal_mul_u12 v t d ht, ← mul_assoc, torus_mul_upperUnipotent3, mul_assoc]
  have hay : (a : v.adicCompletion ℚ) * (d 0 * ((((a : v.adicCompletion ℚ) * d 0)⁻¹) * y₀)) = y₀ := by
    rw [← mul_assoc, mul_inv_cancel_left₀ had0]
  have key : W (iotaGL (diagUnitGL2 a) * t * k₀) = ψ y₀ * W (iotaGL (diagUnitGL2 a) * t * k₀) := by
    calc W (iotaGL (diagUnitGL2 a) * t * k₀)
        = W (iotaGL (diagUnitGL2 a) * t *
            upperUnipotent3 (d 1 * ((((a : v.adicCompletion ℚ) * d 0)⁻¹) * y₀)) 0 0 * k₀) := hfix
      _ = W (upperUnipotent3 y₀ 0 ((a : v.adicCompletion ℚ) * 0) * (iotaGL (diagUnitGL2 a) * t * k₀)) := by
          rw [hmove, mul_assoc, hay]
      _ = ψ (y₀ + 0) * W (iotaGL (diagUnitGL2 a) * t * k₀) := hW y₀ 0 _ _
      _ = ψ y₀ * W (iotaGL (diagUnitGL2 a) * t * k₀) := by rw [add_zero]
  have h0 : (1 - ψ y₀) * W (iotaGL (diagUnitGL2 a) * t * k₀) = 0 := by rw [sub_mul, one_mul, ← key, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (Ne.symm hy₀))

private theorem shellPiece_eq_zero_of_small {ψ : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) (hψ1 : ∀ y, Valued.v y ≤ 1 → ψ y = 1)
    {m : ℕ} (hWm : ∀ u ∈ principalCongruence3 v m, ∀ h, W (h * u) = W h)
    (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (p q r : v.adicCompletion ℚ)
    {t : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d)
    {k₀ : LocalGL3 v} (hk₀ : k₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (u : (v.adicCompletion ℚ)ˣ) (hu1 : Valued.v (u : v.adicCompletion ℚ) = 1) {M : ℕ} (hmM : m ≤ M)
    (huM : Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(M : ℤ))) (hτu : τ u ≠ 1)
    (n : ℤ) (hphase : WithZero.exp (-n) * Valued.v p * WithZero.exp (-(M : ℤ)) ≤ 1) :
    letI := localBorel ℚ v
    ∫ x in valShell v n, torusFn v (fun a => W (iotaGL (diagUnitGL2 a) * (upperUnipotent3 p q r * t * k₀)) *
      ((τ a : ℂˣ) : ℂ)) x ∂selfDualHaarAt ℚ v = 0 := by
  letI := localBorel ℚ v
  refine setIntegral_valShell_eq_zero_of_comp_mul v (u : v.adicCompletion ℚ) hu1 n _ ((τ u : ℂˣ) : ℂ)
    (fun h => hτu (Units.val_eq_one.mp h)) (fun x hx => ?_)
  have hx0 : x ≠ 0 := ne_zero_of_mem_valShell v hx
  have hux0 : (u : v.adicCompletion ℚ) * x ≠ 0 := mul_ne_zero u.ne_zero hx0
  have hmk : Units.mk0 ((u : v.adicCompletion ℚ) * x) hux0 = u * Units.mk0 x hx0 := Units.ext rfl
  have hdu : k₀⁻¹ * iotaGL (diagUnitGL2 u) * k₀ ∈ principalCongruence3 v m := by
    have h := conj_mem_principalCongruence3 v (inv_mem hk₀)
      (principalCongruence3_antitone v hmM (iotaGL_diagUnitGL2_mem_principalCongruence3 v u M hu1 huM))
    rwa [inv_inv] at h

  have hWa : ∀ b : (v.adicCompletion ℚ)ˣ, W (iotaGL (diagUnitGL2 b) * (upperUnipotent3 p q r * t * k₀)) =
      ψ ((b : v.adicCompletion ℚ) * p + q) * W (iotaGL (diagUnitGL2 b) * (t * k₀)) := by
    intro b
    have hg : iotaGL (diagUnitGL2 b) * (upperUnipotent3 p q r * t * k₀) =
        upperUnipotent3 ((b : v.adicCompletion ℚ) * p) q ((b : v.adicCompletion ℚ) * r) *
          (iotaGL (diagUnitGL2 b) * (t * k₀)) := by
      calc iotaGL (diagUnitGL2 b) * (upperUnipotent3 p q r * t * k₀)
          = iotaGL (diagUnitGL2 b) * upperUnipotent3 p q r * t * k₀ := by simp only [mul_assoc]
        _ = upperUnipotent3 ((b : v.adicCompletion ℚ) * p) q ((b : v.adicCompletion ℚ) * r) *
              iotaGL (diagUnitGL2 b) * t * k₀ := by rw [torus_mul_upperUnipotent3]
        _ = _ := by simp only [mul_assoc]
    rw [hg, hW]
  have hWua : W (iotaGL (diagUnitGL2 (u * Units.mk0 x hx0)) * (upperUnipotent3 p q r * t * k₀)) =
      ψ (x * ((u : v.adicCompletion ℚ) * p) + q) * W (iotaGL (diagUnitGL2 (Units.mk0 x hx0)) * (t * k₀)) := by
    have hg : iotaGL (diagUnitGL2 (u * Units.mk0 x hx0)) * (upperUnipotent3 p q r * t * k₀) =
        upperUnipotent3 (x * ((u : v.adicCompletion ℚ) * p)) q (x * ((u : v.adicCompletion ℚ) * r)) *
          (iotaGL (diagUnitGL2 (Units.mk0 x hx0)) * (t * k₀)) * (k₀⁻¹ * iotaGL (diagUnitGL2 u) * k₀) := by
      rw [mul_comm u, iotaGL_diagUnitGL2_mul]
      calc iotaGL (diagUnitGL2 (Units.mk0 x hx0)) * iotaGL (diagUnitGL2 u) * (upperUnipotent3 p q r * t * k₀)
          = iotaGL (diagUnitGL2 (Units.mk0 x hx0)) * (iotaGL (diagUnitGL2 u) * upperUnipotent3 p q r) * t * k₀ := by
            simp only [mul_assoc]
        _ = iotaGL (diagUnitGL2 (Units.mk0 x hx0)) *
              (upperUnipotent3 ((u : v.adicCompletion ℚ) * p) q ((u : v.adicCompletion ℚ) * r) *
                iotaGL (diagUnitGL2 u)) * t * k₀ := by rw [torus_mul_upperUnipotent3]
        _ = iotaGL (diagUnitGL2 (Units.mk0 x hx0)) *
              upperUnipotent3 ((u : v.adicCompletion ℚ) * p) q ((u : v.adicCompletion ℚ) * r) *
                (iotaGL (diagUnitGL2 u) * t) * k₀ := by simp only [mul_assoc]
        _ = iotaGL (diagUnitGL2 (Units.mk0 x hx0)) *
              upperUnipotent3 ((u : v.adicCompletion ℚ) * p) q ((u : v.adicCompletion ℚ) * r) *
                (t * iotaGL (diagUnitGL2 u)) * k₀ := by rw [iotaGL_diagUnitGL2_mul_of_diagonal v u t d ht]
        _ = iotaGL (diagUnitGL2 (Units.mk0 x hx0)) *
              upperUnipotent3 ((u : v.adicCompletion ℚ) * p) q ((u : v.adicCompletion ℚ) * r) * t *
                (k₀ * (k₀⁻¹ * iotaGL (diagUnitGL2 u) * k₀)) := by simp only [mul_assoc, mul_inv_cancel_left]
        _ = upperUnipotent3 (x * ((u : v.adicCompletion ℚ) * p)) q (x * ((u : v.adicCompletion ℚ) * r)) *
              iotaGL (diagUnitGL2 (Units.mk0 x hx0)) * t * (k₀ * (k₀⁻¹ * iotaGL (diagUnitGL2 u) * k₀)) := by
            rw [torus_mul_upperUnipotent3, Units.val_mk0]
        _ = _ := by simp only [mul_assoc]
    rw [hg, hWm _ hdu, hW]

  have hxv : Valued.v x = WithZero.exp (-n) := (mem_valShell v).mp hx
  have hval : Valued.v (x * p * ((u : v.adicCompletion ℚ) - 1)) ≤ 1 := by
    calc Valued.v (x * p * ((u : v.adicCompletion ℚ) - 1))
        = WithZero.exp (-n) * Valued.v p * Valued.v ((u : v.adicCompletion ℚ) - 1) := by rw [map_mul, map_mul, hxv]
      _ ≤ WithZero.exp (-n) * Valued.v p * WithZero.exp (-(M : ℤ)) := mul_le_mul_right huM _
      _ ≤ 1 := hphase
  have hψeq : ψ (x * ((u : v.adicCompletion ℚ) * p) + q) = ψ (x * p + q) := by
    have hsplit : x * ((u : v.adicCompletion ℚ) * p) + q = (x * p + q) + x * p * ((u : v.adicCompletion ℚ) - 1) := by
      ring
    rw [hsplit, AddChar.map_add_eq_mul, hψ1 _ hval, mul_one]
  rw [torusFn_of_ne_zero v _ hux0, torusFn_of_ne_zero v _ hx0]
  rw [hmk, hWua, hWa (Units.mk0 x hx0), Units.val_mk0, hψeq, map_mul, Units.val_mul]
  ring

end TorusLine

section Uniformizer

open Set Filter Topology IsDedekindDomain.HeightOneSpectrum
open scoped NNReal ENNReal Pointwise

private def subBall : Set (v.adicCompletion ℚ) := {x | Valued.v x ≤ WithZero.exp (-1 : ℤ)}

private theorem measurableSet_valBall :
    letI := localBorel ℚ v
    MeasurableSet (valBall v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have : valBall v = Valued.v ⁻¹' Iic 1 := rfl
  rw [this]
  refine measurableSet_preimage_of_mul_invariant_nhds (Valued.v : v.adicCompletion ℚ → WithZero (Multiplicative ℤ)) _
    (ball_one_mem_nhds v) (fun x u hu => ?_) _
  rw [map_mul, valued_eq_one_of_mem_ball v hu, mul_one]

private theorem measurableSet_subBall :
    letI := localBorel ℚ v
    MeasurableSet (subBall v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have : subBall v = Valued.v ⁻¹' Iic (WithZero.exp (-1 : ℤ)) := rfl
  rw [this]
  refine measurableSet_preimage_of_mul_invariant_nhds (Valued.v : v.adicCompletion ℚ → WithZero (Multiplicative ℤ)) _
    (ball_one_mem_nhds v) (fun x u hu => ?_) _
  rw [map_mul, valued_eq_one_of_mem_ball v hu, mul_one]

private theorem exp_neg_one_le_one : WithZero.exp (-1 : ℤ) ≤ 1 :=
  (WithZero.exp_le_exp.mpr (show (-1 : ℤ) ≤ 0 by omega)).trans_eq WithZero.exp_zero

private theorem valBall_eq_biUnion (X : Finset (v.adicCompletion ℚ)) (hX : ∀ r ∈ X, Valued.v r ≤ 1)
    (huniq : ∀ x, Valued.v x ≤ 1 → ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-1 : ℤ)) :
    valBall v = ⋃ r ∈ X, (fun y => -r + y) ⁻¹' subBall v := by
  ext y
  simp only [mem_iUnion, mem_preimage, valBall, subBall, mem_setOf_eq, neg_add_eq_sub]
  constructor
  · intro hy
    obtain ⟨r, ⟨hr, hyr⟩, -⟩ := huniq y hy
    exact ⟨r, hr, hyr⟩
  · rintro ⟨r, hr, hyr⟩
    have hsplit : y = (y - r) + r := by ring
    rw [hsplit]
    exact (Valuation.map_add _ _ _).trans (max_le (hyr.trans (exp_neg_one_le_one)) (hX r hr))

private theorem pairwiseDisjoint_translates (X : Finset (v.adicCompletion ℚ)) (hX : ∀ r ∈ X, Valued.v r ≤ 1)
    (huniq : ∀ x, Valued.v x ≤ 1 → ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-1 : ℤ)) :
    (X : Set (v.adicCompletion ℚ)).PairwiseDisjoint fun r => (fun y => -r + y) ⁻¹' subBall v := by
  intro r hr r' hr' hne
  show Disjoint ((fun y => -r + y) ⁻¹' subBall v) ((fun y => -r' + y) ⁻¹' subBall v)
  rw [Set.disjoint_left]
  intro y hy hy'
  apply hne
  rw [mem_preimage, subBall, mem_setOf_eq, neg_add_eq_sub] at hy hy'
  have hy1 : Valued.v y ≤ 1 := by
    have hsplit : y = (y - r) + r := by ring
    rw [hsplit]
    exact (Valuation.map_add _ _ _).trans (max_le (hy.trans (exp_neg_one_le_one)) (hX r hr))
  obtain ⟨r₀, -, huq⟩ := huniq y hy1
  exact (huq r ⟨hr, hy⟩).trans (huq r' ⟨hr', hy'⟩).symm

private theorem selfDualHaarAt_valBall_eq_card_mul :
    letI := localBorel ℚ v
    selfDualHaarAt ℚ v (valBall v) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) * selfDualHaarAt ℚ v (subBall v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := isAddHaarMeasure_selfDualHaarAt v
  obtain ⟨X, hX, huniq, hcard⟩ := exists_finset_ball_representatives v 0 1 (by norm_num)
  have hX' : ∀ r ∈ X, Valued.v r ≤ 1 := fun r hr => (hX r hr).trans_eq (by rw [neg_zero, WithZero.exp_zero])
  have huniq' : ∀ x, Valued.v x ≤ 1 → ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-1 : ℤ) := fun x hx =>
    huniq x (hx.trans_eq (by rw [neg_zero, WithZero.exp_zero]))
  rw [valBall_eq_biUnion v X hX' huniq',
    measure_biUnion_finset (pairwiseDisjoint_translates v X hX' huniq')
      (fun r _ => (measurable_const_add (-r)) (measurableSet_subBall v))]
  simp_rw [measure_preimage_add]
  rw [Finset.sum_const, nsmul_eq_mul, hcard, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    show ((1 : ℤ) - 0).toNat = 1 by decide, pow_one]

private theorem absNorm_ne_zero' : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 :=
  NumberField.HeightOneSpectrum.absNorm_ne_zero v

private theorem uniformizerUnit_smul_valBall : AdelicLevel.uniformizerUnit ℚ v • valBall v = subBall v := by
  ext y
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Units.smul_def, smul_eq_mul]
    show Valued.v ((AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ) * x) ≤ WithZero.exp (-1 : ℤ)
    rw [map_mul, AdelicLevel.valued_uniformizerUnit]
    exact (mul_le_mul_right (show Valued.v x ≤ 1 from hx) _).trans_eq (mul_one _)
  · intro hy
    refine ⟨(AdelicLevel.uniformizerUnit ℚ v)⁻¹ • y, ?_, smul_inv_smul _ _⟩
    rw [Units.smul_def, smul_eq_mul]
    show Valued.v ((((AdelicLevel.uniformizerUnit ℚ v)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y) ≤ 1
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, AdelicLevel.valued_uniformizerUnit]
    exact (mul_le_mul_right (show Valued.v y ≤ WithZero.exp (-1 : ℤ) from hy) _).trans_eq
      (inv_mul_cancel₀ WithZero.exp_ne_zero)

private theorem distribHaarChar_uniformizerUnit :
    distribHaarChar (v.adicCompletion ℚ) (AdelicLevel.uniformizerUnit ℚ v) = ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := isAddHaarMeasure_selfDualHaarAt v
  haveI := regular_selfDualHaarAt v
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := selfDualHaarAt ℚ v) (s := valBall v)
    (selfDualHaarAt_valBall_ne_zero v) (selfDualHaarAt_valBall_ne_top v) ?_
  rw [uniformizerUnit_smul_valBall, selfDualHaarAt_valBall_eq_card_mul, ENNReal.coe_inv (absNorm_ne_zero' v),
    ENNReal.coe_natCast, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast NumberField.HeightOneSpectrum.absNorm_ne_zero v)
      (ENNReal.natCast_ne_top _), one_mul]

private theorem modulus_varpi : modulus (varpi v) = ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ := by
  show modulus ((AdelicLevel.uniformizerUnit ℚ v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = _
  rw [modulus_coe_units, distribHaarChar_uniformizerUnit]

private theorem valued_uniformizerUnit_zpow (n : ℤ) :
    Valued.v ((AdelicLevel.uniformizerUnit ℚ v ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      WithZero.exp (-n) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zsmul, smul_neg,
    smul_eq_mul, mul_one]

private theorem modulus_eq_of_mem_valShell {k : ℤ} {x : v.adicCompletion ℚ} (hx : x ∈ valShell v k) :
    modulus x = ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ k)⁻¹ := by
  have hx0 : x ≠ 0 := ne_zero_of_mem_valShell v hx
  have hu : Valued.v ((AdelicLevel.uniformizerUnit ℚ v ^ (-k) * Units.mk0 x hx0 : (v.adicCompletion ℚ)ˣ) :
      v.adicCompletion ℚ) = 1 := by
    rw [Units.val_mul, map_mul, valued_uniformizerUnit_zpow, Units.val_mk0, (mem_valShell v).mp hx, neg_neg,
      ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  have hdec : Units.mk0 x hx0 =
      AdelicLevel.uniformizerUnit ℚ v ^ k * (AdelicLevel.uniformizerUnit ℚ v ^ (-k) * Units.mk0 x hx0) := by
    rw [zpow_neg, mul_inv_cancel_left]
  rw [modulus_of_ne_zero hx0, hdec, map_mul, map_zpow, distribHaarChar_uniformizerUnit,
    distribHaarChar_eq_one v _ hu, mul_one, inv_zpow]

private theorem map_mul_left_selfDualHaarAt_of_ne_zero (u : v.adicCompletion ℚ) (hu : u ≠ 0) :
    letI := localBorel ℚ v
    Measure.map (fun x => u * x) (selfDualHaarAt ℚ v) =
      ((distribHaarChar (v.adicCompletion ℚ) (Units.mk0 u hu))⁻¹ : ℝ≥0) • selfDualHaarAt ℚ v := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := isAddHaarMeasure_selfDualHaarAt v
  haveI := regular_selfDualHaarAt v
  ext s hs
  rw [Measure.map_apply (measurable_const_mul u) hs, Measure.smul_apply]
  have hpre : (fun x => u * x) ⁻¹' s = (Units.mk0 u hu)⁻¹ • s := by
    ext x
    rw [mem_preimage, mem_inv_smul_set_iff, Units.smul_def, Units.val_mk0, smul_eq_mul]
  rw [hpre, ← distribHaarChar_mul (μ := selfDualHaarAt ℚ v) (Units.mk0 u hu)⁻¹ s, map_inv, ENNReal.smul_def,
    smul_eq_mul]

private theorem setIntegral_comp_mul_of_ne_zero (u : v.adicCompletion ℚ) (hu : u ≠ 0) (S : Set (v.adicCompletion ℚ))
    (φ : v.adicCompletion ℚ → ℂ) :
    letI := localBorel ℚ v
    ∫ x in (fun x => u * x) ⁻¹' S, φ (u * x) ∂selfDualHaarAt ℚ v =
      (((distribHaarChar (v.adicCompletion ℚ) (Units.mk0 u hu))⁻¹ : ℝ≥0) : ℂ) *
        ∫ y in S, φ y ∂selfDualHaarAt ℚ v := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hmap : (selfDualHaarAt ℚ v).map (MeasurableEquiv.mulLeft₀ u hu) =
      ((distribHaarChar (v.adicCompletion ℚ) (Units.mk0 u hu))⁻¹ : ℝ≥0) • selfDualHaarAt ℚ v := by
    rw [MeasurableEquiv.coe_mulLeft₀]; exact map_mul_left_selfDualHaarAt_of_ne_zero v u hu
  calc ∫ x in (fun x => u * x) ⁻¹' S, φ (u * x) ∂selfDualHaarAt ℚ v
      = ∫ x, φ (MeasurableEquiv.mulLeft₀ u hu x)
          ∂(selfDualHaarAt ℚ v).restrict (MeasurableEquiv.mulLeft₀ u hu ⁻¹' S) := by
        simp_rw [MeasurableEquiv.coe_mulLeft₀]
    _ = ∫ y, φ y ∂((selfDualHaarAt ℚ v).restrict (MeasurableEquiv.mulLeft₀ u hu ⁻¹' S)).map
          (MeasurableEquiv.mulLeft₀ u hu) := (integral_map_equiv _ φ).symm
    _ = ∫ y in S, φ y ∂(((distribHaarChar (v.adicCompletion ℚ) (Units.mk0 u hu))⁻¹ : ℝ≥0) • selfDualHaarAt ℚ v) := by
        rw [← MeasurableEquiv.restrict_map, hmap]
    _ = _ := by
        rw [Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

private theorem preimage_mul_valShell (u : v.adicCompletion ℚ) (j n : ℤ) (hu : Valued.v u = WithZero.exp (-j)) :
    (fun x => u * x) ⁻¹' valShell v n = valShell v (n - j) := by
  ext x
  rw [mem_preimage, mem_valShell, mem_valShell, map_mul, hu]
  constructor
  · intro h
    calc Valued.v x = (WithZero.exp (-j))⁻¹ * (WithZero.exp (-j) * Valued.v x) := by
          rw [← mul_assoc, inv_mul_cancel₀ WithZero.exp_ne_zero, one_mul]
      _ = WithZero.exp (-(n - j)) := by rw [h, ← WithZero.exp_neg, ← WithZero.exp_add]; congr 1; ring
  · intro h
    rw [h, ← WithZero.exp_add]; congr 1; ring

end Uniformizer

section TorusRecurrence

private theorem exists_entriesLE_exp (A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) :
    ∃ a : ℕ, EntriesLE v A (WithZero.exp (a : ℤ)) := by
  have h : ∀ p : Fin 3 × Fin 3, ∃ a : ℕ, Valued.v (A p.1 p.2) ≤ WithZero.exp (a : ℤ) := by
    intro p
    rcases eq_or_ne (Valued.v (A p.1 p.2)) 0 with h0 | h0
    · exact ⟨0, by rw [h0]; exact zero_le'⟩
    · obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (A p.1 p.2) = WithZero.exp m := ⟨_, (WithZero.exp_log h0).symm⟩
      exact ⟨m.toNat, by rw [hm]; exact WithZero.exp_le_exp.mpr (Int.self_le_toNat m)⟩
  choose a ha using h
  refine ⟨Finset.univ.sup a, fun i j => (ha (i, j)).trans (WithZero.exp_le_exp.mpr ?_)⟩
  have h2 : a (i, j) ≤ Finset.univ.sup a := Finset.le_sup (f := a) (Finset.mem_univ (i, j))
  omega

private theorem entriesLE_one : EntriesLE v (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> simp

private theorem exists_forall_conj_mem_principalCongruence3 (g : LocalGL3 v) :
    ∃ L₀ : ℕ, ∀ m : ℕ, ∀ κ ∈ principalCongruence3 v (m + L₀), g⁻¹ * κ * g ∈ principalCongruence3 v m := by
  obtain ⟨a, ha⟩ := exists_entriesLE_exp v ((g⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
  obtain ⟨b, hb⟩ := exists_entriesLE_exp v (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
  refine ⟨a + b, fun m κ hκ => ?_⟩
  have hconj : ∀ {κ' : LocalGL3 v}, κ' ∈ principalCongruence3 v (m + (a + b)) →
      EntriesLE v (((g⁻¹ * κ' * g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1)
        (WithZero.exp (-(m : ℤ))) := by
    intro κ' hκ'
    have hid : ((g⁻¹ * κ' * g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
        ((g⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
          ((κ' : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) *
            (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
      rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]
    rw [hid]
    refine entriesLE_mono v ?_ (entriesLE_mul v (entriesLE_mul v ha hκ'.2) hb)
    rw [← WithZero.exp_add, ← WithZero.exp_add]
    exact WithZero.exp_le_exp.mpr (by omega)
  have hint : ∀ {κ' : LocalGL3 v}, κ' ∈ principalCongruence3 v (m + (a + b)) →
      EntriesLE v ((g⁻¹ * κ' * g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 := by
    intro κ' hκ'
    have h1 : EntriesLE v (((g⁻¹ * κ' * g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) 1 := by
      refine entriesLE_mono v ?_ (hconj hκ')
      rw [← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)
    have h2 := entriesLE_add v h1 (entriesLE_one v)
    rwa [sub_add_cancel] at h2
  have hinv_eq : (g⁻¹ * κ * g)⁻¹ = g⁻¹ * κ⁻¹ * g := by group
  refine ⟨(mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mpr ⟨hint hκ, ?_⟩, hconj hκ⟩
  rw [hinv_eq]
  exact hint (inv_mem hκ)

private theorem exists_level_of_rightTranslate {W : LocalGL3 v → ℂ} {m : ℕ}
    (hW : ∀ κ ∈ principalCongruence3 v m, ∀ y, W (y * κ) = W y) (g : LocalGL3 v) :
    ∃ L : ℕ, ∀ κ ∈ principalCongruence3 v L, ∀ y, W (y * κ * g) = W (y * g) := by
  obtain ⟨L₀, hL₀⟩ := exists_forall_conj_mem_principalCongruence3 v g
  refine ⟨m + L₀, fun κ hκ y => ?_⟩
  have h := hW (g⁻¹ * κ * g) (hL₀ m κ hκ) (y * g)
  rw [← h]
  congr 1
  group

private noncomputable def uniformizerInt : v.adicCompletionIntegers ℚ :=
  ⟨(AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ), by
    show Valued.v (AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ) ≤ 1
    rw [AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by omega)⟩

private theorem algebraMap_uniformizerInt :
    algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (uniformizerInt v) =
      (AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ) :=
  rfl

private theorem algebraMap_uniformizerInt_ne_zero :
    algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (uniformizerInt v) ≠ 0 := by
  rw [algebraMap_uniformizerInt]
  exact Units.ne_zero _

private theorem valued_algebraMap_uniformizerInt :
    Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (uniformizerInt v)) =
      WithZero.exp (-1 : ℤ) := by
  rw [algebraMap_uniformizerInt]
  exact AdelicLevel.valued_uniformizerUnit ℚ v

private theorem iotaGL_diagZ_uniformizerInt (n : ℤ) :
    (iotaGL (UnramifiedWhittaker.diagZ
          (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (uniformizerInt v))
          (algebraMap_uniformizerInt_ne_zero v) n *
        UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (uniformizerInt v))
          (algebraMap_uniformizerInt_ne_zero v) ^ (0 : ℤ)) : LocalGL3 v) =
      iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ n)) := by
  rw [zpow_zero, mul_one]
  congr 1
  apply Units.ext
  show !![algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (uniformizerInt v) ^ n, 0; 0, 1] =
    !![((AdelicLevel.uniformizerUnit ℚ v ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), 0; 0, 1]
  rw [algebraMap_uniformizerInt, Units.val_zpow_eq_zpow_val]

private theorem exists_torus_recurrence_of_normalised (η : AddChar (v.adicCompletion ℚ) ℂ)
    (hη : ¬ ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) → η x = 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn η W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (g₀ : LocalGL3 v) :
    ∃ (L d : ℕ) (c : Fin d → ℂ), ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
      (∀ n : ℤ, n < -(L : ℤ) → W (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ n * u)) * g₀) = 0) ∧
      (∀ n : ℤ, -(L : ℤ) ≤ n →
        W (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ (n + d) * u)) * g₀) =
          ∑ i : Fin d, c i * W (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ (n + (i : ℕ)) * u)) * g₀)) := by
  obtain ⟨m, hm⟩ := exists_level_of_smooth v hsm
  obtain ⟨L, hL⟩ := exists_level_of_rightTranslate v hm g₀
  obtain ⟨d₁, c₁, d₂, c₂, hF⟩ :=
    exists_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_sum_of_isGL3PsiWhittakerFn v
      (algebraMap_uniformizerInt_ne_zero v) (valued_algebraMap_uniformizerInt v) η hη W hW hsm hadm L
  refine ⟨L, d₁, c₁, fun u hu => ?_⟩
  set W₀ : LocalGL3 v → ℂ := gl3AmbientRightTranslate (R := ℂ) g₀ W
  set F : LocalGL3 v → ℂ := gl3AmbientRightTranslate (R := ℂ) (iotaGL (diagUnitGL2 u)) W₀
  have hW₀mem : W₀ ∈ gl3CyclicSubspace W := Submodule.subset_span ⟨g₀, rfl⟩
  have hFmem : F ∈ gl3CyclicSubspace W := gl3AmbientRightTranslate_mem_gl3CyclicSubspace W _ hW₀mem
  have hW₀lev : ∀ κ ∈ principalCongruence3 v L, ∀ y, W₀ (y * κ) = W₀ y := fun κ hκ y => hL κ hκ y
  have hFlev := level_of_translate v hW₀lev (iotaGL_diagUnitGL2_mem_localMaximalCompact3 v u hu)
  have hFinv : ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
      (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(L : ℤ))) →
      ∀ h : LocalGL3 v, F (h * k) = F h := by
    intro k hk hent h
    have hkL : k ∈ principalCongruence3 v L := ⟨hk, fun i j => by rw [Matrix.sub_apply]; exact hent i j⟩
    exact hFlev k hkL h
  obtain ⟨hvan, hrec, -⟩ := hF F hFmem hFinv
  have hpt : ∀ n : ℤ,
      F (iotaGL (UnramifiedWhittaker.diagZ
          (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (uniformizerInt v))
          (algebraMap_uniformizerInt_ne_zero v) n *
        UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (uniformizerInt v))
          (algebraMap_uniformizerInt_ne_zero v) ^ (0 : ℤ))) =
      W (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ n * u)) * g₀) := by
    intro n
    rw [iotaGL_diagZ_uniformizerInt]
    show W (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ n)) * iotaGL (diagUnitGL2 u) * g₀) = _
    rw [iotaGL_diagUnitGL2_mul]
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · have h := hvan n 0 (Or.inl hn)
    rwa [hpt] at h
  · have h := (hrec n 0 hn (by omega)).1
    simp only [hpt] at h
    exact h

end TorusRecurrence

section Normalisation

private theorem admissible_of_intertwining {W : LocalGL3 v → ℂ}
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (e : (LocalGL3 v → ℂ) →ₗ[ℂ] (LocalGL3 v → ℂ)) (he : Function.Injective e) (φ : LocalGL3 v →* LocalGL3 v)
    (hφ : Function.Surjective φ)
    (hφo : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      IsOpen ((Uv.comap φ : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)))
    (hint : ∀ (h : LocalGL3 v) (F : LocalGL3 v → ℂ),
      e (gl3AmbientRightTranslate (R := ℂ) h F) = gl3AmbientRightTranslate (R := ℂ) (φ h) (e F)) :
    ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace (e W),
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)) := by
  intro Uv hUv
  obtain ⟨B, hB⟩ := hadm (Uv.comap φ) (hφo Uv hUv)
  classical
  refine ⟨B.image e, fun F' hF' hinv => ?_⟩
  have hle : gl3CyclicSubspace (e W) ≤ (gl3CyclicSubspace W).map e := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h', rfl⟩
    obtain ⟨h, rfl⟩ := hφ h'
    exact Submodule.mem_map.mpr
      ⟨gl3AmbientRightTranslate (R := ℂ) h W, Submodule.subset_span ⟨h, rfl⟩, hint h W⟩
  obtain ⟨F₀, hF₀, hF₀e⟩ := Submodule.mem_map.mp (hle hF')
  have hinv₀ : ∀ k ∈ Uv.comap φ, ∀ g : LocalGL3 v, F₀ (g * k) = F₀ g := by
    intro k hk g
    have h1 : e (gl3AmbientRightTranslate (R := ℂ) k F₀) = e F₀ := by
      rw [hint, hF₀e]
      funext y
      exact hinv (φ k) hk y
    exact congrFun (he h1) g
  have h2 := Submodule.apply_mem_span_image_of_mem_span e (hB F₀ hF₀ hinv₀)
  rw [← hF₀e, Finset.coe_image]
  exact h2

private noncomputable def leftTranslate (D : LocalGL3 v) : (LocalGL3 v → ℂ) →ₗ[ℂ] (LocalGL3 v → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun h => D * h

private theorem leftTranslate_apply (D : LocalGL3 v) (W : LocalGL3 v → ℂ) (h : LocalGL3 v) :
    leftTranslate v D W h = W (D * h) :=
  rfl

private theorem leftTranslate_injective (D : LocalGL3 v) : Function.Injective (leftTranslate v D) :=
  LinearMap.funLeft_injective_of_surjective ℂ ℂ _ (mul_left_surjective D)

private theorem admissible_leftTranslate {W : LocalGL3 v → ℂ}
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (D : LocalGL3 v) :
    ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace (leftTranslate v D W),
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)) := by
  refine admissible_of_intertwining v hadm (leftTranslate v D) (leftTranslate_injective v D) (MonoidHom.id _)
    Function.surjective_id (fun Uv hUv => ?_) (fun h F => ?_)
  · rw [Subgroup.comap_id]
    exact hUv
  · funext y
    show F (D * y * h) = F (D * (y * h))
    rw [mul_assoc]

private noncomputable def scalingDiag (t : (v.adicCompletion ℚ)ˣ) : LocalGL3 v where
  val := Matrix.diagonal ![((t * t : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), (t : v.adicCompletion ℚ), 1]
  inv := Matrix.diagonal ![(((t * t)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ),
    ((t⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), 1]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
    rw [mul_mul_mul_comm, mul_inv_cancel₀ t.ne_zero, one_mul]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
    rw [mul_mul_mul_comm, inv_mul_cancel₀ t.ne_zero, one_mul]

private theorem scalingDiag_mul_upperUnipotent3 (t : (v.adicCompletion ℚ)ˣ) (x y z : v.adicCompletion ℚ) :
    scalingDiag v t * upperUnipotent3 x y z =
      upperUnipotent3 ((t : v.adicCompletion ℚ) * x) ((t : v.adicCompletion ℚ) * y)
        ((t : v.adicCompletion ℚ) * t * z) * scalingDiag v t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalingDiag, upperUnipotent3, Matrix.mul_apply, Matrix.diagonal]
  ring

private theorem iotaGL_diagUnitGL2_mul_scalingDiag (a t : (v.adicCompletion ℚ)ˣ) :
    iotaGL (diagUnitGL2 a) * scalingDiag v t = scalingDiag v t * iotaGL (diagUnitGL2 a) :=
  iotaGL_diagUnitGL2_mul_of_diagonal v a (scalingDiag v t) _ rfl

private theorem isGL3PsiWhittakerFn_leftTranslate_scalingDiag {η : AddChar (v.adicCompletion ℚ) ℂ}
    {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn η W) (t : (v.adicCompletion ℚ)ˣ) :
    IsGL3PsiWhittakerFn (η.compAddMonoidHom (AddMonoidHom.mulLeft (t : v.adicCompletion ℚ)))
      (leftTranslate v (scalingDiag v t) W) := by
  intro x y z g
  show W (scalingDiag v t * (upperUnipotent3 x y z * g)) =
    η ((t : v.adicCompletion ℚ) * (x + y)) * W (scalingDiag v t * g)
  rw [← mul_assoc, scalingDiag_mul_upperUnipotent3, mul_assoc,
    hW ((t : v.adicCompletion ℚ) * x) ((t : v.adicCompletion ℚ) * y) ((t : v.adicCompletion ℚ) * t * z), mul_add]

private theorem smooth_leftTranslate {W : LocalGL3 v → ℂ}
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g) (D : LocalGL3 v) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, leftTranslate v D W (g * k) = leftTranslate v D W g := by
  obtain ⟨Uv, hUo, hUW⟩ := hsm
  refine ⟨Uv, hUo, fun k hk g => ?_⟩
  show W (D * (g * k)) = W (D * g)
  rw [← mul_assoc]
  exact hUW k hk (D * g)

private theorem exists_zpow_not_forall_eq_one (η : AddChar (v.adicCompletion ℚ) ℂ) (hη : η ≠ 1) :
    ∃ m : ℤ, ¬ ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) →
      η.compAddMonoidHom (AddMonoidHom.mulLeft
        ((AdelicLevel.uniformizerUnit ℚ v ^ m : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) x = 1 := by
  obtain ⟨x₀, hx₀⟩ := AddChar.ne_one_iff.mp hη
  have hx0 : x₀ ≠ 0 := fun h => hx₀ (by rw [h, AddChar.map_zero_eq_one])
  obtain ⟨r, hr⟩ : ∃ r : ℤ, Valued.v x₀ = WithZero.exp r :=
    ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx0)).symm⟩
  refine ⟨1 - r, fun hall => hx₀ ?_⟩
  have h := hall (((AdelicLevel.uniformizerUnit ℚ v ^ (-(1 - r)) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x₀)
    (by
      rw [map_mul, valued_uniformizerUnit_zpow, hr, neg_neg, ← WithZero.exp_add]
      exact WithZero.exp_le_exp.mpr (by omega))
  have h2 : η (((AdelicLevel.uniformizerUnit ℚ v ^ (1 - r) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) *
      (((AdelicLevel.uniformizerUnit ℚ v ^ (-(1 - r)) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x₀)) = 1 := h
  rwa [← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, one_mul] at h2

private theorem exists_torus_recurrence (η : AddChar (v.adicCompletion ℚ) ℂ) (hη : η ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn η W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (g : LocalGL3 v) :
    ∃ (L d : ℕ) (c : Fin d → ℂ), ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
      (∀ n : ℤ, n < -(L : ℤ) → W (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ n * u)) * g) = 0) ∧
      (∀ n : ℤ, -(L : ℤ) ≤ n →
        W (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ (n + d) * u)) * g) =
          ∑ i : Fin d, c i * W (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ (n + (i : ℕ)) * u)) * g)) := by
  obtain ⟨m, hm⟩ := exists_zpow_not_forall_eq_one v η hη
  obtain ⟨L, d, c, hrec⟩ := exists_torus_recurrence_of_normalised v _ hm
    (leftTranslate v (scalingDiag v (AdelicLevel.uniformizerUnit ℚ v ^ m)) W)
    (isGL3PsiWhittakerFn_leftTranslate_scalingDiag v hW _) (smooth_leftTranslate v hsm _)
    (admissible_leftTranslate v hadm _)
    ((scalingDiag v (AdelicLevel.uniformizerUnit ℚ v ^ m))⁻¹ * g)
  refine ⟨L, d, c, fun u hu => ?_⟩
  obtain ⟨h1, h2⟩ := hrec u hu
  have hpt : ∀ n : ℤ,
      leftTranslate v (scalingDiag v (AdelicLevel.uniformizerUnit ℚ v ^ m)) W
        (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ n * u)) *
          ((scalingDiag v (AdelicLevel.uniformizerUnit ℚ v ^ m))⁻¹ * g)) =
      W (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ n * u)) * g) := by
    intro n
    rw [leftTranslate_apply, ← mul_assoc, ← iotaGL_diagUnitGL2_mul_scalingDiag, mul_assoc, mul_inv_cancel_left]
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · rw [← hpt n]
    exact h1 n hn
  · have h := h2 n hn
    simp only [hpt] at h
    exact h

end Normalisation

section UnitsShells

open Set Filter Topology IsDedekindDomain.HeightOneSpectrum
open scoped NNReal ENNReal Pointwise

private theorem valShell_pairwise_disjoint : Pairwise (Function.onFun Disjoint (valShell v)) := by
  intro m n hmn
  show Disjoint (valShell v m) (valShell v n)
  rw [Set.disjoint_left]
  intro x hxm hxn
  have h : WithZero.exp (-m) = WithZero.exp (-n) := by
    rw [← hxm]; exact hxn
  exact hmn (neg_injective (WithZero.exp_injective h))

private theorem iUnion_valShell : ⋃ n : ℤ, valShell v n = {x : v.adicCompletion ℚ | x ≠ 0} := by
  ext x
  simp only [mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨n, hn⟩ rfl
    exact WithZero.exp_ne_zero
      ((map_zero (Valued.v : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ)))).symm.trans hn).symm
  · intro hx
    refine ⟨-WithZero.log (Valued.v x), ?_⟩
    show Valued.v x = WithZero.exp (- -WithZero.log (Valued.v x))
    rw [neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)]

private theorem range_units_val : range (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) = {x | x ≠ 0} := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact u.ne_zero
  · intro hx
    exact ⟨Units.mk0 x hx, rfl⟩

private noncomputable def unitsExt {K : Type*} [GroupWithZero K] {X : Type*} [Zero X] (G : Kˣ → X) (x : K) : X := by
  classical exact if h : x = 0 then 0 else G (Units.mk0 x h)

private theorem unitsExt_coe {K : Type*} [GroupWithZero K] {X : Type*} [Zero X] (G : Kˣ → X) (u : Kˣ) :
    unitsExt G (u : K) = G u := by
  simp [unitsExt, u.ne_zero]

private theorem unitsExt_of_ne_zero {K : Type*} [GroupWithZero K] {X : Type*} [Zero X] (G : Kˣ → X) {x : K}
    (hx : x ≠ 0) : unitsExt G x = G (Units.mk0 x hx) := by
  rw [unitsExt, dif_neg hx]

private theorem measurableEmbedding_units_val {K : Type*} [GroupWithZero K] [MeasurableSpace K]
    [MeasurableSingletonClass K] : MeasurableEmbedding (Units.val : Kˣ → K) where
  injective := Units.val_injective
  measurable := comap_measurable _
  measurableSet_image' := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
    have himg : Units.val '' (Units.val ⁻¹' t : Set Kˣ) = t ∩ {x : K | x ≠ 0} := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨hu, u.ne_zero⟩
      · rintro ⟨hxt, hx0⟩
        exact ⟨Units.mk0 x hx0, by simpa using hxt, rfl⟩
    rw [himg]
    exact ht.inter (measurableSet_singleton (0 : K)).compl

private theorem integral_units_eq_tsum_valShell (G : (v.adicCompletion ℚ)ˣ → ℂ) :
    letI := localBorel ℚ v
    ∀ μ : Measure (v.adicCompletion ℚ)ˣ, Integrable G μ →
      ∫ a, G a ∂μ = ∑' n : ℤ, ∫ a in (Units.val ⁻¹' valShell v n : Set (v.adicCompletion ℚ)ˣ), G a ∂μ := by
  letI := localBorel ℚ v
  intro μ hG
  have hmeas : ∀ n : ℤ, MeasurableSet (Units.val ⁻¹' valShell v n : Set (v.adicCompletion ℚ)ˣ) := fun n =>
    (measurableSet_valShell v n).preimage (comap_measurable _)
  have hcover : (⋃ n : ℤ, (Units.val ⁻¹' valShell v n : Set (v.adicCompletion ℚ)ˣ)) = univ := by
    rw [← preimage_iUnion, iUnion_valShell]
    ext a
    simp
  have hdisj : Pairwise (Function.onFun Disjoint
      fun n : ℤ => (Units.val ⁻¹' valShell v n : Set (v.adicCompletion ℚ)ˣ)) :=
    fun m n hmn => Disjoint.preimage _ (valShell_pairwise_disjoint v hmn)
  rw [← setIntegral_univ, ← hcover]
  exact integral_iUnion hmeas hdisj (hG.integrableOn)

private theorem setIntegral_units_valShell (F : v.adicCompletion ℚ → ℂ) (n : ℤ) :
    letI := localBorel ℚ v
    ∫ a in (Units.val ⁻¹' valShell v n : Set (v.adicCompletion ℚ)ˣ), F (a : v.adicCompletion ℚ)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      ((Ideal.absNorm v.asIdeal : ℝ) ^ n) • ∫ x in valShell v n, F x ∂(selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hemb : MeasurableEmbedding (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) :=
    measurableEmbedding_units_val
  have hS : MeasurableSet (valShell v n) := measurableSet_valShell v n
  have hsub : valShell v n ⊆ range (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) := by
    rw [range_units_val]
    exact fun x hx => ne_zero_of_mem_valShell v hx
  have hsub' : valShell v n ⊆ ({0}ᶜ : Set (v.adicCompletion ℚ)) := by
    intro x hx h0
    rw [mem_singleton_iff] at h0
    exact ne_zero_of_mem_valShell v hx h0
  have hN0 : ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ n) ≠ 0 := zpow_ne_zero n (absNorm_ne_zero' v)

  have h1 : ∫ a in (Units.val ⁻¹' valShell v n : Set (v.adicCompletion ℚ)ˣ), F (a : v.adicCompletion ℚ)
      ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
        ∫ x in valShell v n, F x ∂(mulMeasure (selfDualHaarAt ℚ v)) := by
    rw [← hemb.setIntegral_map F (valShell v n), hemb.map_comap, Measure.restrict_restrict hS,
      inter_eq_left.2 hsub]

  have h2 : (mulMeasure (selfDualHaarAt ℚ v)).restrict (valShell v n) =
      (((Ideal.absNorm v.asIdeal : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) • (selfDualHaarAt ℚ v).restrict (valShell v n) := by
    have hae : (fun x : v.adicCompletion ℚ => ((modulus x : ℝ≥0∞))⁻¹) =ᵐ[(selfDualHaarAt ℚ v).restrict (valShell v n)]
        fun _ => (((Ideal.absNorm v.asIdeal : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) := by
      filter_upwards [ae_restrict_mem hS] with x hx
      show ((modulus x : ℝ≥0∞))⁻¹ = (((Ideal.absNorm v.asIdeal : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞)
      rw [modulus_eq_of_mem_valShell v hx, ENNReal.coe_inv hN0, inv_inv]
    rw [mulMeasure, restrict_withDensity hS, Measure.restrict_restrict hS, inter_eq_left.2 hsub',
      withDensity_congr_ae hae, withDensity_const]
  have h3 : ∫ x in valShell v n, F x ∂(mulMeasure (selfDualHaarAt ℚ v)) =
      ((Ideal.absNorm v.asIdeal : ℝ) ^ n) • ∫ x in valShell v n, F x ∂(selfDualHaarAt ℚ v) := by
    show ∫ x, F x ∂((mulMeasure (selfDualHaarAt ℚ v)).restrict (valShell v n)) = _
    rw [h2, integral_smul_measure, ENNReal.coe_toReal, NNReal.coe_zpow, NNReal.coe_natCast]
  rw [h1, h3]

private noncomputable def zetaFn (W : LocalGL3 v → ℂ) (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v)
    (a : (v.adicCompletion ℚ)ˣ) : ℂ :=
  W (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)

private theorem localZeta30_eq_integral_zetaFn {mT : MeasurableSpace (v.adicCompletion ℚ)ˣ}
    (μ : Measure (v.adicCompletion ℚ)ˣ) (W : LocalGL3 v → ℂ) (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ)
    (g : LocalGL3 v) :
    localZeta30 v μ W τ s g = ∫ a, zetaFn v W τ s g a ∂μ :=
  rfl

private theorem zetaFn_eq_unitsExt (W : LocalGL3 v → ℂ) (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v) :
    zetaFn v W τ s g = fun a : (v.adicCompletion ℚ)ˣ => unitsExt (zetaFn v W τ s g) (a : v.adicCompletion ℚ) :=
  funext fun a => (unitsExt_coe _ a).symm

private theorem setIntegral_valShell_zetaFn (W : LocalGL3 v → ℂ) (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ)
    (g : LocalGL3 v) (n : ℤ) :
    letI := localBorel ℚ v
    ∫ x in valShell v n, unitsExt (zetaFn v W τ s g) x ∂(selfDualHaarAt ℚ v) =
      (((((Ideal.absNorm v.asIdeal : ℝ≥0) ^ n)⁻¹ : ℝ≥0) : ℝ) : ℂ) ^ (s - 1) *
        ∫ x in valShell v n, torusFn v (fun a => W (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ)) x
          ∂(selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_valShell v n) fun x hx => ?_
  have hx0 : x ≠ 0 := ne_zero_of_mem_valShell v hx
  rw [unitsExt_of_ne_zero _ hx0, torusFn_of_ne_zero v _ hx0, zetaFn, Units.val_mk0, modulus_eq_of_mem_valShell v hx]
  ring

private theorem localZeta30_eq_tsum_valShell (W : LocalGL3 v → ℂ) (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ)
    (g : LocalGL3 v) :
    letI := localBorel ℚ v
    Integrable (zetaFn v W τ s g) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) →
      localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ s g =
        ∑' n : ℤ, ((Ideal.absNorm v.asIdeal : ℝ) ^ n) •
          ((((((Ideal.absNorm v.asIdeal : ℝ≥0) ^ n)⁻¹ : ℝ≥0) : ℝ) : ℂ) ^ (s - 1) *
            ∫ x in valShell v n, torusFn v (fun a => W (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ)) x
              ∂(selfDualHaarAt ℚ v)) := by
  letI := localBorel ℚ v
  intro hint
  have hint' : Integrable (fun a : (v.adicCompletion ℚ)ˣ => unitsExt (zetaFn v W τ s g) (a : v.adicCompletion ℚ))
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
    simpa only [unitsExt_coe] using hint
  rw [localZeta30_eq_integral_zetaFn, zetaFn_eq_unitsExt v W τ s g]
  refine (integral_units_eq_tsum_valShell v _ _ hint').trans ?_
  congr 1
  funext n
  rw [setIntegral_units_valShell v (unitsExt (zetaFn v W τ s g)) n, setIntegral_valShell_zetaFn]

end UnitsShells

section ShellCoefficients

open Set MeasureTheory
open scoped NNReal

private theorem hasSum_setIntegral_units_valShell (G : (v.adicCompletion ℚ)ˣ → ℂ) :
    letI := localBorel ℚ v
    ∀ μ : Measure (v.adicCompletion ℚ)ˣ, Integrable G μ →
      HasSum (fun n : ℤ => ∫ a in (Units.val ⁻¹' valShell v n : Set (v.adicCompletion ℚ)ˣ), G a ∂μ) (∫ a, G a ∂μ) := by
  letI := localBorel ℚ v
  intro μ hG
  have hmeas : ∀ n : ℤ, MeasurableSet (Units.val ⁻¹' valShell v n : Set (v.adicCompletion ℚ)ˣ) := fun n =>
    (measurableSet_valShell v n).preimage (comap_measurable _)
  have hcover : (⋃ n : ℤ, (Units.val ⁻¹' valShell v n : Set (v.adicCompletion ℚ)ˣ)) = univ := by
    rw [← preimage_iUnion, iUnion_valShell]
    ext a
    simp
  have hdisj : Pairwise (Function.onFun Disjoint
      fun n : ℤ => (Units.val ⁻¹' valShell v n : Set (v.adicCompletion ℚ)ˣ)) :=
    fun m n hmn => Disjoint.preimage _ (valShell_pairwise_disjoint v hmn)
  rw [← setIntegral_univ, ← hcover]
  exact hasSum_integral_iUnion hmeas hdisj hG.integrableOn

private theorem hasSum_localZeta30_valShell (W : LocalGL3 v → ℂ) (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ)
    (g : LocalGL3 v) :
    letI := localBorel ℚ v
    Integrable (zetaFn v W τ s g) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) →
      HasSum (fun n : ℤ => ((Ideal.absNorm v.asIdeal : ℝ) ^ n) •
          ((((((Ideal.absNorm v.asIdeal : ℝ≥0) ^ n)⁻¹ : ℝ≥0) : ℝ) : ℂ) ^ (s - 1) *
            ∫ x in valShell v n, torusFn v (fun a => W (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ)) x
              ∂(selfDualHaarAt ℚ v)))
        (localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ s g) := by
  letI := localBorel ℚ v
  intro hint
  have hint' : Integrable (fun a : (v.adicCompletion ℚ)ˣ => unitsExt (zetaFn v W τ s g) (a : v.adicCompletion ℚ))
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
    simpa only [unitsExt_coe] using hint
  rw [localZeta30_eq_integral_zetaFn, zetaFn_eq_unitsExt v W τ s g]
  convert hasSum_setIntegral_units_valShell v _ _ hint' using 1
  funext n
  rw [setIntegral_units_valShell v (unitsExt (zetaFn v W τ s g)) n, setIntegral_valShell_zetaFn]

private noncomputable def shellCoeff (W : LocalGL3 v → ℂ) (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v)
    (n : ℤ) : ℂ :=
  letI := localBorel ℚ v
  ∫ x in valShell v 0,
    torusFn v (fun a => W (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ n * a)) * g) * ((τ a : ℂˣ) : ℂ)) x
      ∂(selfDualHaarAt ℚ v)

private theorem uniformizerUnit_zpow_coe_ne_zero (n : ℤ) :
    ((AdelicLevel.uniformizerUnit ℚ v ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≠ 0 :=
  Units.ne_zero _

private theorem torusFn_uniformizerUnit_zpow_mul (W : LocalGL3 v → ℂ) (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (g : LocalGL3 v) (n : ℤ) {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    torusFn v (fun a => W (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ))
        (((AdelicLevel.uniformizerUnit ℚ v ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x) =
      ((τ (AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) ^ n *
        torusFn v (fun a => W (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ n * a)) * g) * ((τ a : ℂˣ) : ℂ))
          x := by
  have hpx : ((AdelicLevel.uniformizerUnit ℚ v ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x ≠ 0 :=
    mul_ne_zero (uniformizerUnit_zpow_coe_ne_zero v n) hx
  have hmk : Units.mk0 (((AdelicLevel.uniformizerUnit ℚ v ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x) hpx =
      AdelicLevel.uniformizerUnit ℚ v ^ n * Units.mk0 x hx :=
    Units.ext (by rw [Units.val_mul, Units.val_mk0, Units.val_mk0])
  rw [torusFn_of_ne_zero v _ hpx, torusFn_of_ne_zero v _ hx, hmk, map_mul, map_zpow, Units.val_mul,
    Units.val_zpow_eq_zpow_val]
  ring

private theorem setIntegral_valShell_torusFn_eq (W : LocalGL3 v → ℂ) (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (g : LocalGL3 v) (n : ℤ) :
    letI := localBorel ℚ v
    ∫ x in valShell v n, torusFn v (fun a => W (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ)) x
        ∂(selfDualHaarAt ℚ v) =
      ((Ideal.absNorm v.asIdeal : ℂ) ^ n)⁻¹ * ((τ (AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) ^ n *
        shellCoeff v W τ g n := by
  letI := localBorel ℚ v
  have hN : (Ideal.absNorm v.asIdeal : ℂ) ^ n ≠ 0 :=
    zpow_ne_zero n (by exact_mod_cast NumberField.HeightOneSpectrum.absNorm_ne_zero v)
  have hcv := setIntegral_comp_mul_of_ne_zero v _ (uniformizerUnit_zpow_coe_ne_zero v n) (valShell v n)
    (torusFn v fun a => W (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ))
  rw [preimage_mul_valShell v _ n n (valued_uniformizerUnit_zpow v n), sub_self, Units.mk0_val, map_zpow,
    distribHaarChar_uniformizerUnit, inv_zpow, inv_inv] at hcv
  have hC : (((((Ideal.absNorm v.asIdeal : ℝ≥0) ^ n : ℝ≥0)) : ℝ) : ℂ) = (Ideal.absNorm v.asIdeal : ℂ) ^ n := by
    push_cast
    rfl
  rw [hC] at hcv
  have hshift : ∫ x in valShell v 0, torusFn v (fun a => W (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ))
        (((AdelicLevel.uniformizerUnit ℚ v ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x)
        ∂(selfDualHaarAt ℚ v) =
      ((τ (AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) ^ n * shellCoeff v W τ g n := by
    rw [shellCoeff, ← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_valShell v 0) fun x hx => ?_
    exact torusFn_uniformizerUnit_zpow_mul v W τ g n (ne_zero_of_mem_valShell v hx)
  rw [hshift] at hcv
  apply mul_left_cancel₀ hN
  rw [← hcv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hN, one_mul]

private theorem shellCoeff_eq_zero (W : LocalGL3 v → ℂ) (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v) (n : ℤ)
    (hvan : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
      W (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ n * u)) * g) = 0) :
    shellCoeff v W τ g n = 0 := by
  letI := localBorel ℚ v
  refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
  have hx0 : x ≠ 0 := ne_zero_of_mem_valShell v hx
  have hx1 : Valued.v ((Units.mk0 x hx0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
    rw [Units.val_mk0, (mem_valShell v).mp hx, neg_zero, WithZero.exp_zero]
  rw [torusFn_of_ne_zero v _ hx0, hvan _ hx1, zero_mul]

end ShellCoefficients

section ShellRecurrence

open Set MeasureTheory
open scoped NNReal ENNReal

private theorem integrableOn_torusFn_valShell (W : LocalGL3 v → ℂ) (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ)
    (g : LocalGL3 v) :
    letI := localBorel ℚ v
    Integrable (zetaFn v W τ s g) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) →
      ∀ n : ℤ, IntegrableOn (torusFn v fun a => W (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ)) (valShell v n)
        (selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  intro hint n
  have hemb : MeasurableEmbedding (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) :=
    measurableEmbedding_units_val
  have hS : MeasurableSet (valShell v n) := measurableSet_valShell v n
  have hsub : valShell v n ⊆ range (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) := by
    rw [range_units_val]
    exact fun x hx => ne_zero_of_mem_valShell v hx
  have hsub' : valShell v n ⊆ ({0}ᶜ : Set (v.adicCompletion ℚ)) := by
    intro x hx h0
    rw [mem_singleton_iff] at h0
    exact ne_zero_of_mem_valShell v hx h0
  have hN0 : ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ n) ≠ 0 := zpow_ne_zero n (absNorm_ne_zero' v)
  have h1 : IntegrableOn (unitsExt (zetaFn v W τ s g)) (valShell v n) (mulMeasure (selfDualHaarAt ℚ v)) := by
    have h0 : IntegrableOn (unitsExt (zetaFn v W τ s g))
        (range (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ)) (mulMeasure (selfDualHaarAt ℚ v)) := by
      rw [IntegrableOn, ← hemb.map_comap, hemb.integrable_map_iff]
      simpa only [Function.comp_def, unitsExt_coe] using hint
    exact h0.mono_set hsub
  have h2 : (mulMeasure (selfDualHaarAt ℚ v)).restrict (valShell v n) =
      (((Ideal.absNorm v.asIdeal : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) • (selfDualHaarAt ℚ v).restrict (valShell v n) := by
    have hae : (fun x : v.adicCompletion ℚ => ((modulus x : ℝ≥0∞))⁻¹) =ᵐ[(selfDualHaarAt ℚ v).restrict (valShell v n)]
        fun _ => (((Ideal.absNorm v.asIdeal : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) := by
      filter_upwards [ae_restrict_mem hS] with x hx
      show ((modulus x : ℝ≥0∞))⁻¹ = (((Ideal.absNorm v.asIdeal : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞)
      rw [modulus_eq_of_mem_valShell v hx, ENNReal.coe_inv hN0, inv_inv]
    rw [mulMeasure, restrict_withDensity hS, Measure.restrict_restrict hS, inter_eq_left.2 hsub',
      withDensity_congr_ae hae, withDensity_const]
  have h3 : IntegrableOn (unitsExt (zetaFn v W τ s g)) (valShell v n) (selfDualHaarAt ℚ v) := by
    have h : Integrable (unitsExt (zetaFn v W τ s g)) ((mulMeasure (selfDualHaarAt ℚ v)).restrict (valShell v n)) := h1
    rw [h2] at h
    exact (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hN0) ENNReal.coe_ne_top).mp h
  have hC : (((((Ideal.absNorm v.asIdeal : ℝ≥0) ^ n)⁻¹ : ℝ≥0) : ℝ) : ℂ) ^ (s - 1) ≠ 0 := by
    intro h
    have hb : (((((Ideal.absNorm v.asIdeal : ℝ≥0) ^ n)⁻¹ : ℝ≥0) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast inv_ne_zero hN0
    exact hb ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have h4 : IntegrableOn
      (fun x => (((((Ideal.absNorm v.asIdeal : ℝ≥0) ^ n)⁻¹ : ℝ≥0) : ℝ) : ℂ) ^ (s - 1) *
        torusFn v (fun a => W (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ)) x)
      (valShell v n) (selfDualHaarAt ℚ v) := by
    refine h3.congr_fun (fun x hx => ?_) hS
    have hx0 : x ≠ 0 := ne_zero_of_mem_valShell v hx
    rw [unitsExt_of_ne_zero _ hx0, torusFn_of_ne_zero v _ hx0, zetaFn, Units.val_mk0, modulus_eq_of_mem_valShell v hx]
    ring
  exact (integrable_const_mul_iff (IsUnit.mk0 _ hC) _).mp h4

private theorem integrableOn_comp_uniformizerUnit_zpow (f : v.adicCompletion ℚ → ℂ) (n : ℤ) :
    letI := localBorel ℚ v
    IntegrableOn f (valShell v n) (selfDualHaarAt ℚ v) →
      IntegrableOn
        (fun x => f (((AdelicLevel.uniformizerUnit ℚ v ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x))
        (valShell v 0) (selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  intro hf
  have hu : ((AdelicLevel.uniformizerUnit ℚ v ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≠ 0 :=
    uniformizerUnit_zpow_coe_ne_zero v n
  have hmap : (selfDualHaarAt ℚ v).map (MeasurableEquiv.mulLeft₀ _ hu) =
      ((distribHaarChar (v.adicCompletion ℚ) (Units.mk0 _ hu))⁻¹ : ℝ≥0) • selfDualHaarAt ℚ v := by
    rw [MeasurableEquiv.coe_mulLeft₀]
    exact map_mul_left_selfDualHaarAt_of_ne_zero v _ hu
  have h1 : IntegrableOn f (valShell v n) ((selfDualHaarAt ℚ v).map (MeasurableEquiv.mulLeft₀ _ hu)) := by
    rw [hmap, IntegrableOn, Measure.restrict_smul]
    exact hf.smul_measure_nnreal
  have h2 := (integrableOn_map_equiv (MeasurableEquiv.mulLeft₀ _ hu)).mp h1
  have hpre : (MeasurableEquiv.mulLeft₀ _ hu) ⁻¹' valShell v n = valShell v 0 := by
    rw [MeasurableEquiv.coe_mulLeft₀]
    have h := preimage_mul_valShell v _ n n (valued_uniformizerUnit_zpow v n)
    rwa [sub_self] at h
  rw [hpre] at h2
  refine h2.congr_fun (fun x _ => ?_) (measurableSet_valShell v 0)
  simp only [Function.comp_apply, MeasurableEquiv.coe_mulLeft₀]

private theorem integrableOn_shellCoeff_integrand (W : LocalGL3 v → ℂ) (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ)
    (g : LocalGL3 v) :
    letI := localBorel ℚ v
    Integrable (zetaFn v W τ s g) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) →
      ∀ n : ℤ, IntegrableOn
        (torusFn v fun a => W (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ n * a)) * g) * ((τ a : ℂˣ) : ℂ))
        (valShell v 0) (selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  intro hint n
  have h1 := integrableOn_comp_uniformizerUnit_zpow v _ n (integrableOn_torusFn_valShell v W τ s g hint n)
  have h2 : IntegrableOn
      (fun x => ((τ (AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) ^ n *
        torusFn v
          (fun a => W (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ n * a)) * g) * ((τ a : ℂˣ) : ℂ)) x)
      (valShell v 0) (selfDualHaarAt ℚ v) :=
    h1.congr_fun (fun x hx => torusFn_uniformizerUnit_zpow_mul v W τ g n (ne_zero_of_mem_valShell v hx))
      (measurableSet_valShell v 0)
  exact (integrable_const_mul_iff (IsUnit.mk0 _ (zpow_ne_zero n (Units.ne_zero _))) _).mp h2

private theorem shellCoeff_recurrence (W : LocalGL3 v → ℂ) (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v)
    (n : ℤ) (d : ℕ) (c : Fin d → ℂ) :
    letI := localBorel ℚ v
    (∀ k : ℤ, IntegrableOn
        (torusFn v fun a => W (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ k * a)) * g) * ((τ a : ℂˣ) : ℂ))
        (valShell v 0) (selfDualHaarAt ℚ v)) →
      (∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
        W (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ (n + d) * u)) * g) =
          ∑ i : Fin d, c i * W (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ (n + (i : ℕ)) * u)) * g)) →
      shellCoeff v W τ g (n + d) = ∑ i : Fin d, c i * shellCoeff v W τ g (n + (i : ℕ)) := by
  letI := localBorel ℚ v
  intro hint hrec
  simp only [shellCoeff]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum Finset.univ fun (i : Fin d) _ => Integrable.const_mul (hint (n + (i : ℕ))) (c i)]
  refine setIntegral_congr_fun (measurableSet_valShell v 0) fun x hx => ?_
  have hx0 : x ≠ 0 := ne_zero_of_mem_valShell v hx
  have hx1 : Valued.v ((Units.mk0 x hx0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
    rw [Units.val_mk0, (mem_valShell v).mp hx, neg_zero, WithZero.exp_zero]
  simp only [torusFn_of_ne_zero v _ hx0]
  rw [hrec _ hx1, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _

private theorem ofReal_zpow_cpow {r : ℝ} (hr : 0 < r) (n : ℤ) (w : ℂ) : ((r : ℂ) ^ n) ^ w = ((r : ℂ) ^ w) ^ n := by
  rw [← Complex.cpow_int_mul, ← Complex.cpow_intCast, ← Complex.cpow_mul]
  · rw [← Complex.ofReal_log hr.le, ← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.ofReal_im]
    exact neg_lt_zero.mpr Real.pi_pos
  · rw [← Complex.ofReal_log hr.le, ← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.ofReal_im]
    exact Real.pi_pos.le

private theorem absNorm_inv_zpow_cpow (n : ℤ) (w : ℂ) :
    (((Ideal.absNorm v.asIdeal : ℂ)⁻¹) ^ n) ^ w = (((Ideal.absNorm v.asIdeal : ℂ)⁻¹) ^ w) ^ n := by
  have hpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero
      (by exact_mod_cast NumberField.HeightOneSpectrum.absNorm_ne_zero v)))
  have h := ofReal_zpow_cpow hpos n w
  push_cast at h
  exact h

private theorem absNorm_inv_cpow_sub_one (s : ℂ) :
    ((Ideal.absNorm v.asIdeal : ℂ)⁻¹) ^ (s - 1) =
      (Ideal.absNorm v.asIdeal : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) := by
  have hN : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast NumberField.HeightOneSpectrum.absNorm_ne_zero v
  rw [Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_pos.ne), Complex.cpow_sub _ _ hN,
    Complex.cpow_one, Complex.cpow_neg, inv_div, div_eq_mul_inv]

private noncomputable def shellVar (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ((τ (AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ)⁻¹) ^ (s - 1)

private theorem shellVar_eq (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) :
    shellVar v τ s =
      ((τ (AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) := by
  rw [shellVar, absNorm_inv_cpow_sub_one, mul_assoc]

private theorem coe_absNorm_zpow_inv_eq (n : ℤ) :
    (((((Ideal.absNorm v.asIdeal : ℝ≥0) ^ n)⁻¹ : ℝ≥0) : ℝ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℂ)⁻¹) ^ n := by
  simp only [NNReal.coe_inv, NNReal.coe_zpow, NNReal.coe_natCast, Complex.ofReal_inv, Complex.ofReal_zpow,
    Complex.ofReal_natCast, inv_zpow]

private theorem shellTerm_eq (W : LocalGL3 v → ℂ) (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v)
    (n : ℤ) :
    letI := localBorel ℚ v
    ((Ideal.absNorm v.asIdeal : ℝ) ^ n) •
        ((((((Ideal.absNorm v.asIdeal : ℝ≥0) ^ n)⁻¹ : ℝ≥0) : ℝ) : ℂ) ^ (s - 1) *
          ∫ x in valShell v n, torusFn v (fun a => W (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ)) x
            ∂(selfDualHaarAt ℚ v)) =
      shellCoeff v W τ g n * shellVar v τ s ^ n := by
  letI := localBorel ℚ v
  have hN : (Ideal.absNorm v.asIdeal : ℂ) ^ n ≠ 0 :=
    zpow_ne_zero n (by exact_mod_cast NumberField.HeightOneSpectrum.absNorm_ne_zero v)
  rw [setIntegral_valShell_torusFn_eq, coe_absNorm_zpow_inv_eq, absNorm_inv_zpow_cpow, Complex.real_smul,
    Complex.ofReal_zpow, Complex.ofReal_natCast, shellVar, mul_zpow]
  field_simp

private theorem hasSum_shellCoeff_mul_shellVar_zpow (W : LocalGL3 v → ℂ) (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ)
    (g : LocalGL3 v) :
    letI := localBorel ℚ v
    Integrable (zetaFn v W τ s g) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) →
      HasSum (fun n : ℤ => shellCoeff v W τ g n * shellVar v τ s ^ n)
        (localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ s g) := by
  letI := localBorel ℚ v
  intro hint
  convert hasSum_localZeta30_valShell v W τ s g hint using 1
  funext n
  exact (shellTerm_eq v W τ s g n).symm

end ShellRecurrence

section RationalGeneratingFunction

open Polynomial

section Recurrence

private noncomputable def recurrenceDenominator (d : ℕ) (c : Fin d → ℂ) : ℂ[X] :=
  1 - ∑ i : Fin d, C (c i) * X ^ (d - (i : ℕ))

private theorem recurrenceDenominator_coeff_zero (d : ℕ) (c : Fin d → ℂ) :
    (recurrenceDenominator d c).coeff 0 = 1 := by
  unfold recurrenceDenominator
  rw [coeff_sub, coeff_one_zero, finsetSum_coeff]
  have h : ∀ i : Fin d, (C (c i) * X ^ (d - (i : ℕ)) : ℂ[X]).coeff 0 = 0 := by
    intro i
    have hi : ¬ (0 = d - (i : ℕ)) := by
      have := i.isLt
      omega
    rw [coeff_C_mul, coeff_X_pow, if_neg hi, mul_zero]
  rw [Finset.sum_eq_zero fun i _ => h i, sub_zero]

private theorem recurrenceDenominator_ne_zero (d : ℕ) (c : Fin d → ℂ) : recurrenceDenominator d c ≠ 0 := by
  intro h
  have h0 := recurrenceDenominator_coeff_zero d c
  rw [h, coeff_zero] at h0
  exact zero_ne_one h0

private theorem eval_recurrenceDenominator (d : ℕ) (c : Fin d → ℂ) (Y : ℂ) :
    (recurrenceDenominator d c).eval Y = 1 - ∑ i : Fin d, c i * Y ^ (d - (i : ℕ)) := by
  simp [recurrenceDenominator, eval_finsetSum]

private noncomputable def recurrenceNumerator (γ : ℕ → ℂ) (d : ℕ) (c : Fin d → ℂ) : ℂ[X] :=
  (∑ m ∈ Finset.range d, C (γ m) * X ^ m) -
    ∑ i : Fin d, C (c i) * X ^ (d - (i : ℕ)) * ∑ m ∈ Finset.range (i : ℕ), C (γ m) * X ^ m

private theorem eval_recurrenceNumerator (γ : ℕ → ℂ) (d : ℕ) (c : Fin d → ℂ) (Y : ℂ) :
    (recurrenceNumerator γ d c).eval Y =
      (∑ m ∈ Finset.range d, γ m * Y ^ m) -
        ∑ i : Fin d, c i * Y ^ (d - (i : ℕ)) * ∑ m ∈ Finset.range (i : ℕ), γ m * Y ^ m := by
  simp [recurrenceNumerator, eval_finsetSum]

private theorem eval_recurrenceDenominator_mul_of_hasSum (γ : ℕ → ℂ) (d : ℕ) (c : Fin d → ℂ)
    (hrec : ∀ m : ℕ, γ (m + d) = ∑ i : Fin d, c i * γ (m + (i : ℕ))) (Y S : ℂ)
    (hS : HasSum (fun m : ℕ => γ m * Y ^ m) S) :
    (recurrenceDenominator d c).eval Y * S = (recurrenceNumerator γ d c).eval Y := by
  have htail : ∀ k : ℕ,
      HasSum (fun m : ℕ => γ (m + k) * Y ^ (m + k)) (S - ∑ m ∈ Finset.range k, γ m * Y ^ m) :=
    fun k => (hasSum_nat_add_iff' k).mpr hS
  have hzero : HasSum (fun m : ℕ => γ (m + d) * Y ^ (m + d) -
      ∑ i : Fin d, c i * Y ^ (d - (i : ℕ)) * (γ (m + (i : ℕ)) * Y ^ (m + (i : ℕ)))) 0 := by
    have hfun : (fun m : ℕ => γ (m + d) * Y ^ (m + d) -
        ∑ i : Fin d, c i * Y ^ (d - (i : ℕ)) * (γ (m + (i : ℕ)) * Y ^ (m + (i : ℕ)))) = fun _ => (0 : ℂ) := by
      funext m
      have hpow : ∀ i : Fin d, Y ^ (d - (i : ℕ)) * Y ^ (m + (i : ℕ)) = Y ^ (m + d) := by
        intro i
        rw [← pow_add]
        congr 1
        have := i.isLt
        omega
      calc γ (m + d) * Y ^ (m + d) - ∑ i : Fin d, c i * Y ^ (d - (i : ℕ)) * (γ (m + (i : ℕ)) * Y ^ (m + (i : ℕ)))
          = γ (m + d) * Y ^ (m + d) - ∑ i : Fin d, c i * γ (m + (i : ℕ)) * Y ^ (m + d) := by
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← hpow i]
            ring
        _ = (γ (m + d) - ∑ i : Fin d, c i * γ (m + (i : ℕ))) * Y ^ (m + d) := by
            rw [sub_mul, Finset.sum_mul]
        _ = 0 := by rw [hrec m, sub_self, zero_mul]
    rw [hfun]
    exact hasSum_zero
  have hsum : HasSum (fun m : ℕ => γ (m + d) * Y ^ (m + d) -
      ∑ i : Fin d, c i * Y ^ (d - (i : ℕ)) * (γ (m + (i : ℕ)) * Y ^ (m + (i : ℕ))))
      ((S - ∑ m ∈ Finset.range d, γ m * Y ^ m) -
        ∑ i : Fin d, c i * Y ^ (d - (i : ℕ)) * (S - ∑ m ∈ Finset.range (i : ℕ), γ m * Y ^ m)) :=
    (htail d).sub (hasSum_sum fun i _ => (htail (i : ℕ)).mul_left (c i * Y ^ (d - (i : ℕ))))
  have hkey := hzero.unique hsum
  have hexp : ∑ i : Fin d, c i * Y ^ (d - (i : ℕ)) * (S - ∑ m ∈ Finset.range (i : ℕ), γ m * Y ^ m) =
      (∑ i : Fin d, c i * Y ^ (d - (i : ℕ))) * S -
        ∑ i : Fin d, c i * Y ^ (d - (i : ℕ)) * ∑ m ∈ Finset.range (i : ℕ), γ m * Y ^ m := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hexp] at hkey
  rw [eval_recurrenceDenominator, eval_recurrenceNumerator]
  linear_combination -hkey

private theorem hasSum_nat_sub_of_hasSum_int (f : ℤ → ℂ) (L : ℕ) (hf : ∀ n : ℤ, n < -(L : ℤ) → f n = 0) (Z : ℂ)
    (hZ : HasSum f Z) : HasSum (fun m : ℕ => f ((m : ℤ) - L)) Z := by
  have hinj : Function.Injective (fun m : ℕ => (m : ℤ) - L) := by
    intro a b h
    have h' : (a : ℤ) - L = (b : ℤ) - L := h
    omega
  have hsupp : ∀ n : ℤ, n ∉ Set.range (fun m : ℕ => (m : ℤ) - L) → f n = 0 := by
    intro n hn
    refine hf n ?_
    by_contra hge
    refine hn ⟨(n + L).toNat, ?_⟩
    show (((n + L).toNat : ℕ) : ℤ) - L = n
    rw [Int.toNat_of_nonneg (a := n + L) (by omega)]
    ring
  exact (hinj.hasSum_iff hsupp).mpr hZ

private theorem exists_polynomial_of_recurrence (β : ℤ → ℂ) (L d : ℕ) (c : Fin d → ℂ)
    (hvan : ∀ n : ℤ, n < -(L : ℤ) → β n = 0)
    (hrec : ∀ n : ℤ, -(L : ℤ) ≤ n → β (n + d) = ∑ i : Fin d, c i * β (n + (i : ℕ))) :
    ∃ P Q : ℂ[X], Q ≠ 0 ∧
      ∀ (Y Z : ℂ), Y ≠ 0 → HasSum (fun n : ℤ => β n * Y ^ n) Z → Q.eval Y * Z = P.eval Y := by
  have hrecγ : ∀ m : ℕ, (fun m : ℕ => β ((m : ℤ) - L)) (m + d) =
      ∑ i : Fin d, c i * (fun m : ℕ => β ((m : ℤ) - L)) (m + (i : ℕ)) := by
    intro m
    have h := hrec ((m : ℤ) - L) (by omega)
    have h1 : (((m + d : ℕ) : ℤ) - L) = (m : ℤ) - L + d := by omega
    have h2 : ∀ i : Fin d, (((m + (i : ℕ) : ℕ) : ℤ) - L) = (m : ℤ) - L + (i : ℕ) := fun i => by omega
    show β (((m + d : ℕ) : ℤ) - L) = ∑ i : Fin d, c i * β (((m + (i : ℕ) : ℕ) : ℤ) - L)
    rw [h1, h]
    exact Finset.sum_congr rfl fun i _ => by rw [h2 i]
  refine ⟨recurrenceNumerator (fun m : ℕ => β ((m : ℤ) - L)) d c, X ^ L * recurrenceDenominator d c,
    mul_ne_zero (pow_ne_zero _ X_ne_zero) (recurrenceDenominator_ne_zero d c), ?_⟩
  intro Y Z hY hZ
  have h1 : HasSum (fun m : ℕ => β ((m : ℤ) - L) * Y ^ ((m : ℤ) - L)) Z :=
    hasSum_nat_sub_of_hasSum_int (fun n : ℤ => β n * Y ^ n) L
      (fun n hn => by
        show β n * Y ^ n = 0
        rw [hvan n hn, zero_mul]) Z hZ
  have h3 : HasSum (fun m : ℕ => Y ^ L * (β ((m : ℤ) - L) * Y ^ ((m : ℤ) - L))) (Y ^ L * Z) := h1.mul_left (Y ^ L)
  have hfun : (fun m : ℕ => Y ^ L * (β ((m : ℤ) - L) * Y ^ ((m : ℤ) - L))) =
      fun m : ℕ => β ((m : ℤ) - L) * Y ^ m := by
    funext m
    rw [zpow_sub₀ hY, zpow_natCast, zpow_natCast]
    field_simp
  rw [hfun] at h3
  have hmain := eval_recurrenceDenominator_mul_of_hasSum (fun m : ℕ => β ((m : ℤ) - L)) d c hrecγ Y (Y ^ L * Z) h3
  rw [eval_mul, eval_pow, eval_X]
  linear_combination hmain

end Recurrence

section Substitution

private theorem comp_C_mul_X_ne_zero {Q : ℂ[X]} (hQ : Q ≠ 0) {a : ℂ} (ha : a ≠ 0) : Q.comp (C a * X) ≠ 0 := by
  intro h
  rcases comp_eq_zero_iff.mp h with h0 | ⟨_, hc⟩
  · exact hQ h0
  · have h1 : a = 0 := by simpa using congrArg (fun p : ℂ[X] => p.coeff 1) hc
    exact ha h1

private theorem eval_comp_C_mul_X (P : ℂ[X]) (a Y : ℂ) : (P.comp (C a * X)).eval Y = P.eval (a * Y) := by
  rw [eval_comp, eval_mul, eval_C, eval_X]

private theorem exists_polynomial_comp (P Q : ℂ[X]) (hQ : Q ≠ 0) (a : ℂ) (ha : a ≠ 0) :
    ∃ P' Q' : ℂ[X], Q' ≠ 0 ∧ ∀ (Y Z : ℂ), Q.eval (a * Y) * Z = P.eval (a * Y) → Q'.eval Y * Z = P'.eval Y :=
  ⟨P.comp (C a * X), Q.comp (C a * X), comp_C_mul_X_ne_zero hQ ha, fun Y Z h => by
    rw [eval_comp_C_mul_X, eval_comp_C_mul_X]
    exact h⟩

private theorem exists_polynomial_reflect (P Q : ℂ[X]) (hQ : Q ≠ 0) (a : ℂ) (ha : a ≠ 0) :
    ∃ P' Q' : ℂ[X], Q' ≠ 0 ∧
      ∀ (Y Z : ℂ), Y ≠ 0 → Q.eval (a * Y⁻¹) * Z = P.eval (a * Y⁻¹) → Q'.eval Y * Z = P'.eval Y := by
  refine ⟨reflect (max (P.comp (C a * X)).natDegree (Q.comp (C a * X)).natDegree) (P.comp (C a * X)),
    reflect (max (P.comp (C a * X)).natDegree (Q.comp (C a * X)).natDegree) (Q.comp (C a * X)),
    fun h => comp_C_mul_X_ne_zero hQ ha (reflect_eq_zero_iff.mp h), ?_⟩
  intro Y Z hY h
  set D := max (P.comp (C a * X)).natDegree (Q.comp (C a * X)).natDegree with hD
  letI : Invertible (Y⁻¹) := invertibleOfNonzero (inv_ne_zero hY)
  have hinv : (⅟(Y⁻¹) : ℂ) = Y := by rw [invOf_eq_inv, inv_inv]
  have hP := eval₂_reflect_mul_pow (RingHom.id ℂ) Y⁻¹ D (P.comp (C a * X)) (le_max_left _ _)
  have hQ' := eval₂_reflect_mul_pow (RingHom.id ℂ) Y⁻¹ D (Q.comp (C a * X)) (le_max_right _ _)
  rw [hinv] at hP hQ'
  have hPe : (reflect D (P.comp (C a * X))).eval Y * Y⁻¹ ^ D = P.eval (a * Y⁻¹) := by
    rw [← eval_comp_C_mul_X]
    exact hP
  have hQe : (reflect D (Q.comp (C a * X))).eval Y * Y⁻¹ ^ D = Q.eval (a * Y⁻¹) := by
    rw [← eval_comp_C_mul_X]
    exact hQ'
  have hYD : Y⁻¹ ^ D * Y ^ D = 1 := by rw [← mul_pow, inv_mul_cancel₀ hY, one_pow]
  calc (reflect D (Q.comp (C a * X))).eval Y * Z
      = (reflect D (Q.comp (C a * X))).eval Y * Y⁻¹ ^ D * Z * Y ^ D := by
        linear_combination (-((reflect D (Q.comp (C a * X))).eval Y * Z)) * hYD
    _ = P.eval (a * Y⁻¹) * Y ^ D := by rw [hQe, h]
    _ = (reflect D (P.comp (C a * X))).eval Y * Y⁻¹ ^ D * Y ^ D := by rw [hPe]
    _ = (reflect D (P.comp (C a * X))).eval Y := by rw [mul_assoc, hYD, mul_one]

end Substitution

end RationalGeneratingFunction

section Main

open Polynomial

private theorem shellVar_ne_zero (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) : shellVar v τ s ≠ 0 := by
  rw [shellVar_eq]
  have hN : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast NumberField.HeightOneSpectrum.absNorm_ne_zero v
  refine mul_ne_zero (mul_ne_zero (Units.ne_zero _) hN) fun h => hN ?_
  exact ((Complex.cpow_eq_zero_iff _ _).mp h).1

private theorem exists_polynomial_localZeta30 (η : AddChar (v.adicCompletion ℚ) ℂ) (hη : η ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn η W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v) (σ₀ : ℝ) :
    letI := localBorel ℚ v
    IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ g σ₀ →
      ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ ∀ s : ℂ, σ₀ < s.re →
        Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
            localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ s g =
          P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
  letI := localBorel ℚ v
  intro hconv
  obtain ⟨L, d, c, hrec⟩ := exists_torus_recurrence v η hη W hW hsm hadm g
  have hvan : ∀ n : ℤ, n < -(L : ℤ) → shellCoeff v W τ g n = 0 := fun n hn =>
    shellCoeff_eq_zero v W τ g n fun u hu => (hrec u hu).1 n hn
  have hint := integrableOn_shellCoeff_integrand v W τ ((σ₀ : ℂ) + 1) g (hconv _ (by simp))
  have hrec' : ∀ n : ℤ, -(L : ℤ) ≤ n →
      shellCoeff v W τ g (n + d) = ∑ i : Fin d, c i * shellCoeff v W τ g (n + (i : ℕ)) := fun n hn =>
    shellCoeff_recurrence v W τ g n d c hint fun u hu => (hrec u hu).2 n hn
  obtain ⟨P₀, Q₀, hQ₀, hPQ₀⟩ := exists_polynomial_of_recurrence (shellCoeff v W τ g) L d c hvan hrec'
  have hN : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast NumberField.HeightOneSpectrum.absNorm_ne_zero v
  obtain ⟨P, Q, hQ, hPQ⟩ := exists_polynomial_comp P₀ Q₀ hQ₀
    (((τ (AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ))
    (mul_ne_zero (Units.ne_zero _) hN)
  refine ⟨P, Q, hQ, fun s hs => hPQ _ _ ?_⟩
  have hsum := hasSum_shellCoeff_mul_shellVar_zpow v W τ s g (hconv s hs)
  have hY := shellVar_ne_zero v τ s
  rw [shellVar_eq] at hsum hY
  exact hPQ₀ _ _ hY hsum

end Main

section TransposeInverse

variable {v}

open scoped Matrix

private theorem transposeInv3_one : (transposeInv3 (1 : LocalGL3 v)) = 1 := by
  apply Units.ext
  show (((1 : LocalGL3 v)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ᵀ = _
  simp

private theorem transposeInv3_mul (g k : LocalGL3 v) : transposeInv3 (g * k) = transposeInv3 g * transposeInv3 k := by
  apply Units.ext
  show ((((g * k)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))ᵀ =
    (((g⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))ᵀ *
      (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))ᵀ
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem continuous_transposeInv3 : Continuous fun g : LocalGL3 v => transposeInv3 g := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_coe_inv.matrix_transpose
  · exact Units.continuous_val.matrix_transpose

private theorem dualWhittakerFn3_right_invariant (W : LocalGL3 v → ℂ) (Uv : Subgroup (LocalGL3 v))
    (hinv : ∀ k ∈ Uv, ∀ h : LocalGL3 v, W (h * k) = W h) :
    ∀ k ∈ (fun g : LocalGL3 v => transposeInv3 g) ⁻¹' (Uv : Set (LocalGL3 v)), ∀ h : LocalGL3 v,
      dualWhittakerFn3 W (h * k) = dualWhittakerFn3 W h := by
  intro k hk h
  simp only [dualWhittakerFn3_apply, transposeInv3_mul, ← mul_assoc]
  exact hinv _ hk _

private theorem isOpen_transposeInv3_preimage (Uv : Subgroup (LocalGL3 v)) (hU : IsOpen (Uv : Set (LocalGL3 v))) :
    IsOpen ((fun g : LocalGL3 v => transposeInv3 g) ⁻¹' (Uv : Set (LocalGL3 v))) :=
  hU.preimage continuous_transposeInv3

private theorem one_mem_transposeInv3_preimage (Uv : Subgroup (LocalGL3 v)) :
    (1 : LocalGL3 v) ∈ (fun g : LocalGL3 v => transposeInv3 g) ⁻¹' (Uv : Set (LocalGL3 v)) := by
  show transposeInv3 (1 : LocalGL3 v) ∈ Uv
  rw [transposeInv3_one]
  exact Uv.one_mem

private theorem coe_lowerUnipotent21_inv (x : v.adicCompletion ℚ) :
    (((lowerUnipotent21 x)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1, 0, 0; -x, 1, 0; 0, 0, 1] :=
  rfl

private
theorem continuous_lowerUnipotent21 : Continuous fun x : v.adicCompletion ℚ => (lowerUnipotent21 x : LocalGL3 v) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · simp only [Function.comp_def, lowerUnipotent21_coe]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · simp_rw [coe_lowerUnipotent21_inv]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

end TransposeInverse

section SecondCountable

private theorem secondCountableTopology_adicCompletion : SecondCountableTopology (v.adicCompletion ℚ) := by
  haveI : Countable (WithVal (v.valuation ℚ)) := (WithVal.equiv (v.valuation ℚ)).injective.countable
  haveI : TopologicalSpace.SeparableSpace (v.adicCompletion ℚ) := inferInstance
  exact UniformSpace.secondCountable_of_separable (v.adicCompletion ℚ)

end SecondCountable

section DualReduction

open Polynomial

private theorem smooth_dualWhittakerFn3 {W : LocalGL3 v → ℂ}
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, dualWhittakerFn3 W (g * k) = dualWhittakerFn3 W g := by
  obtain ⟨Uv, hUv, hinv⟩ := hsm
  refine ⟨Uv.comap (MonoidHom.mk' (fun g : LocalGL3 v => transposeInv3 g) transposeInv3_mul), ?_, ?_⟩
  · exact isOpen_transposeInv3_preimage Uv hUv
  · intro k hk g
    exact dualWhittakerFn3_right_invariant W Uv hinv k hk g

private theorem isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace {ψ : AddChar (v.adicCompletion ℚ) ℂ}
    {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn ψ W) {F : LocalGL3 v → ℂ} (hF : F ∈ gl3CyclicSubspace W) :
    IsGL3PsiWhittakerFn ψ F := by
  have hle : gl3CyclicSubspace W ≤ gl3PsiWhittakerFnSpace (v.adicCompletion ℚ) ℂ ψ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    exact rightTranslate_mem_gl3PsiWhittakerFnSpace ψ h ((mem_gl3PsiWhittakerFnSpace_iff ψ W).mpr hW)
  exact (mem_gl3PsiWhittakerFnSpace_iff ψ F).mp (hle hF)

private theorem exists_level_of_mem_gl3CyclicSubspace {W : LocalGL3 v → ℂ} {m : ℕ}
    (hW : ∀ κ ∈ principalCongruence3 v m, ∀ y, W (y * κ) = W y) {F : LocalGL3 v → ℂ}
    (hF : F ∈ gl3CyclicSubspace W) :
    ∃ M : ℕ, ∀ κ ∈ principalCongruence3 v M, ∀ y, F (y * κ) = F y := by
  have hF' : F ∈ Submodule.span ℂ (Set.range fun h : LocalGL3 v => gl3AmbientRightTranslate (R := ℂ) h W) := hF
  refine Submodule.span_induction
    (p := fun F _ => ∃ M : ℕ, ∀ κ ∈ principalCongruence3 v M, ∀ y, F (y * κ) = F y) ?_ ?_ ?_ ?_ hF'
  · rintro _ ⟨h, rfl⟩
    obtain ⟨M, hM⟩ := exists_level_of_rightTranslate v hW h
    exact ⟨M, fun κ hκ y => hM κ hκ y⟩
  · exact ⟨0, fun _ _ _ => rfl⟩
  · rintro F₁ F₂ _ _ ⟨M₁, h₁⟩ ⟨M₂, h₂⟩
    refine ⟨max M₁ M₂, fun κ hκ y => ?_⟩
    have hκ₁ := principalCongruence3_antitone v (le_max_left M₁ M₂) hκ
    have hκ₂ := principalCongruence3_antitone v (le_max_right M₁ M₂) hκ
    show F₁ (y * κ) + F₂ (y * κ) = F₁ y + F₂ y
    rw [h₁ κ hκ₁ y, h₂ κ hκ₂ y]
  · rintro a F _ ⟨M, h⟩
    refine ⟨M, fun κ hκ y => ?_⟩
    show a * F (y * κ) = a * F y
    rw [h κ hκ y]

private theorem smooth_of_mem_gl3CyclicSubspace {W : LocalGL3 v → ℂ}
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    {F : LocalGL3 v → ℂ} (hF : F ∈ gl3CyclicSubspace W) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g := by
  obtain ⟨m, hm⟩ := exists_level_of_smooth v hsm
  obtain ⟨M, hM⟩ := exists_level_of_mem_gl3CyclicSubspace v hm hF
  exact ⟨principalCongruence3 v M, isOpen_principalCongruence3 v M, hM⟩

private theorem gl3CyclicSubspace_le_of_mem {W F : LocalGL3 v → ℂ} (hF : F ∈ gl3CyclicSubspace W) :
    gl3CyclicSubspace F ≤ gl3CyclicSubspace W := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨h, rfl⟩
  exact gl3AmbientRightTranslate_mem_gl3CyclicSubspace W h hF

private theorem admissible_of_gl3CyclicSubspace_le {W F : LocalGL3 v → ℂ}
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ G ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (hle : gl3CyclicSubspace F ≤ gl3CyclicSubspace W) :
    ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ G ∈ gl3CyclicSubspace F,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)) := by
  intro Uv hUv
  obtain ⟨B, hB⟩ := hadm Uv hUv
  exact ⟨B, fun G hG hGinv => hB G (hle hG) hGinv⟩

private theorem isLocalZeta30ConvergentAbove_of_isLocalZeta31ConvergentAbove (W' : LocalGL3 v → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (h₀ : LocalGL3 v) (σ : ℝ) (Vd : LocalGL3 v → ℂ) :
    letI := localBorel ℚ v
    (∀ a : (v.adicCompletion ℚ)ˣ,
        (∫ x, W' (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h₀) ∂(selfDualHaarAt ℚ v)) =
          Vd (iotaGL (diagUnitGL2 a))) →
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        W' χ h₀ σ →
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) Vd χ 1 σ := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := secondCountableTopology_adicCompletion v
  haveI := isAddHaarMeasure_selfDualHaarAt v
  haveI : SigmaFinite (selfDualHaarAt ℚ v) := sigmaFinite_of_locallyFinite
  intro hVd h31 s hs
  refine (h31 s hs).integral_prod_left.congr (Filter.Eventually.of_forall fun a => ?_)
  show (∫ x, W' (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h₀) * ((χ a : ℂˣ) : ℂ) *
      ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) ∂(selfDualHaarAt ℚ v)) =
    Vd (iotaGL (diagUnitGL2 a) * 1) * ((χ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)
  rw [integral_mul_const, integral_mul_const, hVd a, mul_one]

private theorem localZetaDual31_eq_localZeta30 (W : LocalGL3 v → ℂ) (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (w : ℂ)
    (g : LocalGL3 v) (Vd : LocalGL3 v → ℂ) :
    letI := localBorel ℚ v
    (∀ a : (v.adicCompletion ℚ)ˣ,
        (∫ x, dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 g))
            ∂(selfDualHaarAt ℚ v)) =
          Vd (iotaGL (diagUnitGL2 a))) →
      localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W τ w g =
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) Vd τ⁻¹ w 1 := by
  letI := localBorel ℚ v
  intro hVd
  unfold localZetaDual31 localZeta31 localZeta30
  simp_rw [hVd, mul_one]

private theorem absNorm_cpow_neg_one_sub (s : ℂ) :
    (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)) =
      (Ideal.absNorm v.asIdeal : ℂ)⁻¹ * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  have hN : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast NumberField.HeightOneSpectrum.absNorm_ne_zero v
  rw [neg_sub, Complex.cpow_sub _ _ hN, Complex.cpow_one, Complex.cpow_neg, inv_inv, div_eq_inv_mul]

private theorem exists_polynomial_localZetaDual31 (η' : AddChar (v.adicCompletion ℚ) ℂ) (hη' : η' ≠ 1)
    (W : LocalGL3 v → ℂ) (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v) (σ₁ : ℝ) (Vd : LocalGL3 v → ℂ)
    (hVdW : IsGL3PsiWhittakerFn η' Vd)
    (hVdsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ h : LocalGL3 v, Vd (h * k) = Vd h)
    (hVdadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ G ∈ gl3CyclicSubspace Vd,
        (∀ k ∈ Uv, ∀ h : LocalGL3 v, G (h * k) = G h) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) :
    letI := localBorel ℚ v
    (∀ a : (v.adicCompletion ℚ)ˣ,
        (∫ x, dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 g))
            ∂(selfDualHaarAt ℚ v)) =
          Vd (iotaGL (diagUnitGL2 a))) →
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        (dualWhittakerFn3 W) τ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ →
      ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ ∀ s : ℂ, σ₁ < (1 - s).re →
        Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
            localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W τ
              (1 - s) g =
          P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
  letI := localBorel ℚ v
  intro hVd h31
  have hconv := isLocalZeta30ConvergentAbove_of_isLocalZeta31ConvergentAbove v (dualWhittakerFn3 W) τ⁻¹ _ σ₁ Vd hVd h31
  obtain ⟨P₀, Q₀, hQ₀, h₀⟩ := exists_polynomial_localZeta30 v η' hη' Vd hVdW hVdsm hVdadm τ⁻¹ 1 σ₁ hconv
  have hN : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast NumberField.HeightOneSpectrum.absNorm_ne_zero v
  obtain ⟨P, Q, hQ, hPQ⟩ := exists_polynomial_reflect P₀ Q₀ hQ₀ _ (inv_ne_zero hN)
  refine ⟨P, Q, hQ, fun s hs => hPQ _ _ (fun h => hN ((Complex.cpow_eq_zero_iff _ _).mp h).1) ?_⟩
  rw [localZetaDual31_eq_localZeta30 v W τ (1 - s) g Vd hVd, ← absNorm_cpow_neg_one_sub]
  exact h₀ (1 - s) hs

end DualReduction

section CyclicTranslates

private theorem translate_mem_gl3CyclicSubspace (W : LocalGL3 v → ℂ) (g : LocalGL3 v) :
    (fun h => W (h * g)) ∈ gl3CyclicSubspace W :=
  Submodule.subset_span ⟨g, funext fun _ => rfl⟩

end CyclicTranslates

section DualUnipotent

open Set Filter Topology IsDedekindDomain.HeightOneSpectrum
open scoped NNReal ENNReal Matrix

private theorem lowerUnipotent21_mul (x y : v.adicCompletion ℚ) :
    (lowerUnipotent21 x : LocalGL3 v) * lowerUnipotent21 y = lowerUnipotent21 (x + y) := by
  apply Units.ext
  rw [Units.val_mul, lowerUnipotent21_coe, lowerUnipotent21_coe, lowerUnipotent21_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem exists_level_of_translate {W : LocalGL3 v → ℂ}
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ u ∈ Uv, ∀ g, W (g * u) = W g)
    (h₀ : LocalGL3 v) : ∃ m : ℕ, ∀ u ∈ principalCongruence3 v m, ∀ g, W (g * u * h₀) = W (g * h₀) := by
  obtain ⟨Uv, hUo, hUW⟩ := hsm
  have hcont : Continuous fun u : LocalGL3 v => h₀⁻¹ * u * h₀⁻¹⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hopen : IsOpen ((Uv.comap (MulAut.conj h₀⁻¹).toMonoidHom : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) :=
    hUo.preimage hcont
  obtain ⟨m, hm⟩ := exists_principalCongruence3_le_of_isOpen v _ hopen
  refine ⟨m, fun u hu g => ?_⟩
  have hu' : h₀⁻¹ * u * h₀⁻¹⁻¹ ∈ Uv := hm hu
  rw [inv_inv] at hu'
  calc W (g * u * h₀) = W (g * h₀ * (h₀⁻¹ * u * h₀)) := by
        rw [← mul_assoc, ← mul_assoc, mul_inv_cancel_right]
    _ = W (g * h₀) := hUW _ hu' _

private theorem diagonal_mul_u23 (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) (y : v.adicCompletion ℚ) :
    t * upperUnipotent3 0 (d 2 * y) 0 = upperUnipotent3 0 (d 1 * y) 0 * t := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ht]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Matrix.mul_apply, Matrix.diagonal]
  ring

private
theorem u23_inv (y : v.adicCompletion ℚ) : (upperUnipotent3 0 y 0 : LocalGL3 v)⁻¹ = upperUnipotent3 0 (-y) 0 := by
  apply Units.ext
  show (upperUnipotent3 0 y 0 : LocalGL3 v).inv =
    ((upperUnipotent3 0 (-y) 0 : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3]

private
theorem entriesLE_u23_sub_one {y : v.adicCompletion ℚ} {e : WithZero (Multiplicative ℤ)} (hy : Valued.v y ≤ e) :
    EntriesLE v (((upperUnipotent3 0 y 0 : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) e := by
  intro i j
  rw [Matrix.sub_apply]
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, hy]

private
theorem u23_mem_principalCongruence3 {m : ℕ} {y : v.adicCompletion ℚ} (hy : Valued.v y ≤ WithZero.exp (-(m : ℤ))) :
    upperUnipotent3 0 y 0 ∈ principalCongruence3 v m := by
  have hy1 : Valued.v y ≤ 1 :=
    hy.trans ((WithZero.exp_le_exp.mpr (show (-(m : ℤ)) ≤ 0 by omega)).trans_eq WithZero.exp_zero)
  refine ⟨(mem_localMaximalCompact3_iff (R := 𝓞 ℚ) (K := ℚ) (v := v)).mpr ⟨fun i j => ?_, fun i j => ?_⟩,
    entriesLE_u23_sub_one v hy⟩
  · fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, hy1]
  · rw [u23_inv]
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, hy1]

private theorem whittaker_diag_eq_zero_of_large_second {ψ : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) {m : ℕ} (hWm : ∀ u ∈ principalCongruence3 v m, ∀ h, W (h * u) = W h)
    {t : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) (hd1 : d 1 ≠ 0)
    {k₀ : LocalGL3 v} (hk₀ : k₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) {y₀ : v.adicCompletion ℚ} (hy₀ : ψ y₀ ≠ 1)
    (h : Valued.v (d 2) * Valued.v y₀ ≤ WithZero.exp (-(m : ℤ)) * Valued.v (d 1)) :
    W (t * k₀) = 0 := by
  have hsmall : Valued.v (d 2 * ((d 1)⁻¹ * y₀)) ≤ WithZero.exp (-(m : ℤ)) := by
    calc Valued.v (d 2 * ((d 1)⁻¹ * y₀))
        = Valued.v (d 2) * Valued.v y₀ * (Valued.v (d 1))⁻¹ := by
          rw [map_mul, map_mul, map_inv₀, mul_comm ((Valued.v (d 1))⁻¹) (Valued.v y₀), mul_assoc]
      _ ≤ WithZero.exp (-(m : ℤ)) * Valued.v (d 1) * (Valued.v (d 1))⁻¹ := mul_le_mul_left h _
      _ = WithZero.exp (-(m : ℤ)) := by
          rw [mul_assoc, mul_inv_cancel₀ ((Valuation.ne_zero_iff _).mpr hd1), mul_one]
  have hfix : W (t * k₀) = W (t * upperUnipotent3 0 (d 2 * ((d 1)⁻¹ * y₀)) 0 * k₀) :=
    (level_of_translate v hWm hk₀ _ (u23_mem_principalCongruence3 v hsmall) _).symm
  have hdy : d 1 * ((d 1)⁻¹ * y₀) = y₀ := mul_inv_cancel_left₀ hd1 y₀
  have key : W (t * k₀) = ψ y₀ * W (t * k₀) := by
    calc W (t * k₀) = W (t * upperUnipotent3 0 (d 2 * ((d 1)⁻¹ * y₀)) 0 * k₀) := hfix
      _ = W (upperUnipotent3 0 y₀ 0 * (t * k₀)) := by rw [diagonal_mul_u23 v t d ht, hdy, mul_assoc]
      _ = ψ (0 + y₀) * W (t * k₀) := hW 0 y₀ 0 _
      _ = ψ y₀ * W (t * k₀) := by rw [zero_add]
  have h0 : (1 - ψ y₀) * W (t * k₀) = 0 := by rw [sub_mul, one_mul, ← key, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (Ne.symm hy₀))

private noncomputable def lowerIwasawaK (x : v.adicCompletion ℚ) : LocalGL3 v where
  val := !![0, -1, 0; 1, x⁻¹, 0; 0, 0, 1]
  inv := !![x⁻¹, 1, 0; -1, 0, 0; 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private noncomputable def lowerIwasawaT (x : v.adicCompletion ℚ) (hx : x ≠ 0) : LocalGL3 v where
  val := Matrix.diagonal ![x⁻¹, x, 1]
  inv := Matrix.diagonal ![x, x⁻¹, 1]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hx]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hx]

private theorem coe_lowerIwasawaT (x : v.adicCompletion ℚ) (hx : x ≠ 0) :
    ((lowerIwasawaT v x hx : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![x⁻¹, x, 1] :=
  rfl

private theorem lowerIwasawaK_mem (x : v.adicCompletion ℚ) (h1 : 1 ≤ Valued.v x) :
    lowerIwasawaK v x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have hxi : (Valued.v x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  refine (mem_localMaximalCompact3_iff (R := 𝓞 ℚ) (K := ℚ) (v := v)).mpr ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [lowerIwasawaK, map_inv₀, hxi]
  · show Valued.v ((lowerIwasawaK v x).inv i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [lowerIwasawaK, map_inv₀, hxi]

private theorem lowerUnipotent21_eq (x : v.adicCompletion ℚ) (hx : x ≠ 0) :
    (lowerUnipotent21 x : LocalGL3 v) = upperUnipotent3 x⁻¹ 0 0 * lowerIwasawaT v x hx * lowerIwasawaK v x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, lowerUnipotent21_coe, coe_lowerIwasawaT, upperUnipotent3_coe]
  have hT : (Matrix.diagonal ![x⁻¹, x, 1] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![x⁻¹, 0, 0; 0, x, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h1 : x⁻¹ * x = 1 := inv_mul_cancel₀ hx
  have h2 : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  rw [hT]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerIwasawaK, Matrix.mul_apply, Fin.sum_univ_three, h1, h2]

private theorem lowerUnipotent21_zero : (lowerUnipotent21 (0 : v.adicCompletion ℚ) : LocalGL3 v) = 1 := by
  apply Units.ext
  rw [lowerUnipotent21_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem transposeInv3_transposeInv3 (g : LocalGL3 v) : transposeInv3 (transposeInv3 g) = g := by
  apply Units.ext
  show (((g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ᵀ)ᵀ = _
  exact Matrix.transpose_transpose _

private theorem exists_forall_torus_lowerUnipotent21_eq_zero {ψ : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) (hψ : ∃ y₀ : v.adicCompletion ℚ, ψ y₀ ≠ 1)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ u ∈ Uv, ∀ g, W (g * u) = W g)
    (h₀ : LocalGL3 v) :
    ∃ R : ℤ, ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ), WithZero.exp R < Valued.v x →
      W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h₀) = 0 := by
  obtain ⟨m, hm⟩ := exists_level_of_translate v hsm h₀
  obtain ⟨y₀, hy₀⟩ := hψ
  have hy0 : y₀ ≠ 0 := by
    rintro rfl
    exact hy₀ (AddChar.map_zero_eq_one ψ)
  obtain ⟨e₀, he₀⟩ : ∃ e : ℤ, Valued.v y₀ = WithZero.exp e :=
    ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hy0)).symm⟩
  refine ⟨max 0 (e₀ + m), fun a x hx => ?_⟩
  have h1 : 1 ≤ Valued.v x := by
    rw [← WithZero.exp_zero]
    exact (WithZero.exp_le_exp.mpr (le_max_left _ _)).trans hx.le
  have hx0 : x ≠ 0 := fun h0 => by
    rw [h0, map_zero] at h1
    exact not_lt.mpr h1 zero_lt_one
  have hlarge : WithZero.exp (e₀ + m) ≤ Valued.v x := (WithZero.exp_le_exp.mpr (le_max_right _ _)).trans hx.le

  have hW₀ : IsGL3PsiWhittakerFn ψ fun g => W (g * h₀) := fun p q r g => by
    show W (upperUnipotent3 p q r * g * h₀) = ψ (p + q) * W (g * h₀)
    rw [mul_assoc]
    exact hW p q r (g * h₀)
  have ht : ((iotaGL (diagUnitGL2 a) * lowerIwasawaT v x hx0 : LocalGL3 v) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal ![(a : v.adicCompletion ℚ) * x⁻¹, x, 1] := by
    rw [Units.val_mul, coe_iotaGL_diagUnitGL2, coe_lowerIwasawaT, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp
  have hkill : W (iotaGL (diagUnitGL2 a) * lowerIwasawaT v x hx0 * lowerIwasawaK v x * h₀) = 0 := by
    refine whittaker_diag_eq_zero_of_large_second v hW₀ hm ht hx0 (lowerIwasawaK_mem v x h1) hy₀ ?_
    show Valued.v (1 : v.adicCompletion ℚ) * Valued.v y₀ ≤ WithZero.exp (-(m : ℤ)) * Valued.v x
    rw [map_one, one_mul, he₀]
    calc WithZero.exp e₀ = WithZero.exp (-(m : ℤ)) * WithZero.exp (e₀ + m) := by
          rw [← WithZero.exp_add]
          congr 1
          ring
      _ ≤ WithZero.exp (-(m : ℤ)) * Valued.v x := mul_le_mul_right hlarge _
  have hmat : iotaGL (diagUnitGL2 a) * (upperUnipotent3 x⁻¹ 0 0 * lowerIwasawaT v x hx0 * lowerIwasawaK v x) * h₀ =
      upperUnipotent3 ((a : v.adicCompletion ℚ) * x⁻¹) 0 ((a : v.adicCompletion ℚ) * 0) *
        (iotaGL (diagUnitGL2 a) * lowerIwasawaT v x hx0 * lowerIwasawaK v x * h₀) := by
    simp only [← mul_assoc, torus_mul_upperUnipotent3]
  rw [lowerUnipotent21_eq v x hx0, hmat, hW, hkill, mul_zero]

private theorem exists_nhds_forall_lowerUnipotent21_add_eq {W : LocalGL3 v → ℂ}
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ u ∈ Uv, ∀ g, W (g * u) = W g)
    (h₀ : LocalGL3 v) :
    ∃ U ∈ 𝓝 (0 : v.adicCompletion ℚ), ∀ (h : LocalGL3 v) (x : v.adicCompletion ℚ), ∀ ε ∈ U,
      W (h * lowerUnipotent21 (x + ε) * h₀) = W (h * lowerUnipotent21 x * h₀) := by
  obtain ⟨Uv, hUo, hUW⟩ := hsm
  have hcont : Continuous fun ε : v.adicCompletion ℚ => h₀⁻¹ * (lowerUnipotent21 ε : LocalGL3 v) * h₀ :=
    (continuous_const.mul continuous_lowerUnipotent21).mul continuous_const
  have hzero :
      (fun ε : v.adicCompletion ℚ => h₀⁻¹ * (lowerUnipotent21 ε : LocalGL3 v) * h₀) 0 ∈ (Uv : Set (LocalGL3 v)) := by
    show h₀⁻¹ * (lowerUnipotent21 0 : LocalGL3 v) * h₀ ∈ (Uv : Set (LocalGL3 v))
    rw [lowerUnipotent21_zero, mul_one, inv_mul_cancel]
    exact Uv.one_mem
  refine ⟨(fun ε : v.adicCompletion ℚ => h₀⁻¹ * (lowerUnipotent21 ε : LocalGL3 v) * h₀) ⁻¹' (Uv : Set (LocalGL3 v)),
    hcont.continuousAt.preimage_mem_nhds (hUo.mem_nhds hzero), fun h x ε hε => ?_⟩
  have hε' : h₀⁻¹ * (lowerUnipotent21 ε : LocalGL3 v) * h₀ ∈ Uv := hε
  calc W (h * lowerUnipotent21 (x + ε) * h₀)
      = W (h * lowerUnipotent21 x * h₀ * (h₀⁻¹ * lowerUnipotent21 ε * h₀)) := by
        rw [← lowerUnipotent21_mul]
        simp only [← mul_assoc, mul_inv_cancel_right]
    _ = W (h * lowerUnipotent21 x * h₀) := hUW _ hε' _

private theorem exists_mem_gl3CyclicSubspace_integral_lowerUnipotent21_eq {ψ : AddChar (v.adicCompletion ℚ) ℂ}
    {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn ψ W) (hψ : ∃ y₀ : v.adicCompletion ℚ, ψ y₀ ≠ 1)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ u ∈ Uv, ∀ g, W (g * u) = W g)
    (h₀ : LocalGL3 v) :
    ∃ Vd ∈ gl3CyclicSubspace W, ∀ a : (v.adicCompletion ℚ)ˣ,
      (letI := localBorel ℚ v
       ∫ x, W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h₀) ∂(selfDualHaarAt ℚ v)) =
        Vd (iotaGL (diagUnitGL2 a)) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := isAddHaarMeasure_selfDualHaarAt v
  obtain ⟨R, hR⟩ := exists_forall_torus_lowerUnipotent21_eq_zero v hW hψ hsm h₀
  obtain ⟨U, hU, hloc⟩ := exists_nhds_forall_lowerUnipotent21_add_eq v hsm h₀

  obtain ⟨Φ, hΦ⟩ :
      ∃ Φ : v.adicCompletion ℚ → (LocalGL3 v → ℂ), ∀ x, Φ x = fun h => W (h * (lowerUnipotent21 x * h₀)) :=
    ⟨_, fun _ => rfl⟩
  have hΦmem : ∀ x, Φ x ∈ gl3CyclicSubspace W := fun x => by
    rw [hΦ]
    exact translate_mem_gl3CyclicSubspace v W _
  have hΦlc : IsLocallyConstant Φ := by
    refine (IsLocallyConstant.iff_eventually_eq Φ).mpr fun x => ?_
    have hs : (fun y => y - x) ⁻¹' U ∈ 𝓝 x :=
      (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
        (by show U ∈ 𝓝 (x - x); rw [sub_self]; exact hU)
    filter_upwards [hs] with y hy
    have hxy : x + (y - x) = y := by ring
    rw [hΦ, hΦ]
    funext h
    calc W (h * (lowerUnipotent21 y * h₀))
        = W (h * lowerUnipotent21 (x + (y - x)) * h₀) := by rw [hxy, mul_assoc]
      _ = W (h * lowerUnipotent21 x * h₀) := hloc h x _ hy
      _ = W (h * (lowerUnipotent21 x * h₀)) := by rw [mul_assoc]

  have hBc : IsCompact {x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (-(-R))} :=
    isCompact_setOf_valued_sub_le v 0 (-R)
  have hBm : MeasurableSet {x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (-(-R))} :=
    (isClopen_setOf_valued_sub_le v 0 (-R)).isClosed.measurableSet
  have hfin : (Φ '' {x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (-(-R))}).Finite := by
    haveI := isCompact_iff_compactSpace.mp hBc
    rw [Set.image_eq_range]
    exact (hΦlc.comp_continuous continuous_subtype_val).range_finite

  refine ⟨fun h => ∫ x in {x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (-(-R))}, Φ x h
      ∂(selfDualHaarAt ℚ v), ?_, fun a => ?_⟩
  ·
    classical
    have hdec : (fun h => ∫ x in {x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (-(-R))}, Φ x h
        ∂(selfDualHaarAt ℚ v)) = ∑ φ ∈ hfin.toFinset,
          (((selfDualHaarAt ℚ v).real ({x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (-(-R))} ∩
            {x | Φ x = φ}) : ℝ) : ℂ) • φ := by
      funext h
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      have hcover : {x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (-(-R))} =
          ⋃ φ ∈ hfin.toFinset,
            ({x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (-(-R))} ∩ {x | Φ x = φ}) := by
        ext x
        constructor
        · intro hx
          exact Set.mem_iUnion₂.mpr ⟨Φ x, hfin.mem_toFinset.mpr ⟨x, hx, rfl⟩, hx, rfl⟩
        · intro hx
          obtain ⟨φ, -, hx'⟩ := Set.mem_iUnion₂.mp hx
          exact hx'.1
      conv_lhs => rw [hcover]
      rw [integral_biUnion_finset hfin.toFinset (fun φ _ => hBm.inter (hΦlc.isOpen_fiber φ).measurableSet)]
      · refine Finset.sum_congr rfl fun φ _ => ?_
        rw [setIntegral_congr_fun (hBm.inter (hΦlc.isOpen_fiber φ).measurableSet)
          (fun x hx => show Φ x h = φ h by rw [hx.2]), setIntegral_const, Complex.real_smul]
      · intro φ _ φ' _ hne
        refine Set.disjoint_left.mpr fun x hx hx' => hne ?_
        rw [← hx.2, ← hx'.2]
      · intro φ _
        refine (integrableOn_const (C := φ h)
          ((measure_mono Set.inter_subset_left).trans_lt hBc.measure_lt_top).ne).congr_fun
          (fun x hx => show φ h = Φ x h by rw [hx.2]) (hBm.inter (hΦlc.isOpen_fiber φ).measurableSet)
    rw [hdec]
    refine Submodule.sum_mem _ fun φ hφ => Submodule.smul_mem _ _ ?_
    obtain ⟨x, -, rfl⟩ := hfin.mem_toFinset.mp hφ
    exact hΦmem x
  ·
    have hfun : (fun x => W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h₀)) =
        fun x => Φ x (iotaGL (diagUnitGL2 a)) := by
      funext x
      rw [hΦ, mul_assoc]
    show ∫ x, W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h₀) ∂(selfDualHaarAt ℚ v) =
      ∫ x in {x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (-(-R))}, Φ x (iotaGL (diagUnitGL2 a))
        ∂(selfDualHaarAt ℚ v)
    rw [hfun, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [Set.mem_setOf_eq, sub_zero, neg_neg, not_le] at hx
    show Φ x (iotaGL (diagUnitGL2 a)) = 0
    rw [hΦ]
    show W (iotaGL (diagUnitGL2 a) * (lowerUnipotent21 x * h₀)) = 0
    rw [← mul_assoc]
    exact hR a x hx

private theorem dualWhittakerFn3_translate (f : LocalGL3 v → ℂ) (g : LocalGL3 v) :
    dualWhittakerFn3 (fun h => f (h * g)) = fun h => dualWhittakerFn3 f (h * transposeInv3 g) := by
  funext h
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul, transposeInv3_transposeInv3, mul_assoc]

private theorem dualWhittakerFn3_mem_gl3CyclicSubspace {W f : LocalGL3 v → ℂ} (hf : f ∈ gl3CyclicSubspace W) :
    dualWhittakerFn3 f ∈ gl3CyclicSubspace (dualWhittakerFn3 W) := by
  refine Submodule.span_induction (p := fun f _ => dualWhittakerFn3 f ∈ gl3CyclicSubspace (dualWhittakerFn3 W))
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨g, rfl⟩
    show dualWhittakerFn3 (fun h => W (h * g)) ∈ gl3CyclicSubspace (dualWhittakerFn3 W)
    rw [dualWhittakerFn3_translate]
    exact translate_mem_gl3CyclicSubspace v (dualWhittakerFn3 W) (transposeInv3 g)
  · exact Submodule.zero_mem _
  · intro f₁ f₂ _ _ h₁ h₂
    exact Submodule.add_mem _ h₁ h₂
  · intro c f _ h
    exact Submodule.smul_mem _ c h

end DualUnipotent

section DualInstance

private noncomputable def transposeInv3Hom : LocalGL3 v →* LocalGL3 v :=
  MonoidHom.mk' (fun g => transposeInv3 g) transposeInv3_mul

private theorem surjective_longWeyl3_mul_transposeInv3 :
    Function.Surjective fun h : LocalGL3 v => longWeyl3 * transposeInv3 h := by
  intro z
  refine ⟨transposeInv3 (longWeyl3⁻¹ * z), ?_⟩
  show longWeyl3 * transposeInv3 (transposeInv3 (longWeyl3⁻¹ * z)) = z
  rw [transposeInv3_transposeInv3, mul_inv_cancel_left]

private theorem admissible_dualWhittakerFn3 {W : LocalGL3 v → ℂ}
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) :
    ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace (dualWhittakerFn3 W),
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)) := by
  refine admissible_of_intertwining v hadm (LinearMap.funLeft ℂ ℂ fun h : LocalGL3 v => longWeyl3 * transposeInv3 h)
    (LinearMap.funLeft_injective_of_surjective ℂ ℂ _ (surjective_longWeyl3_mul_transposeInv3 (v := v)))
    (transposeInv3Hom v) (fun y => ⟨transposeInv3 y, transposeInv3_transposeInv3 v y⟩) (fun Uv hUv => ?_)
    (fun h F => ?_)
  · rw [Subgroup.coe_comap]
    exact isOpen_transposeInv3_preimage Uv hUv
  · funext y
    show F (longWeyl3 * transposeInv3 y * h) = F (longWeyl3 * transposeInv3 (y * transposeInv3 h))
    rw [transposeInv3_mul, transposeInv3_transposeInv3, mul_assoc]

private theorem exists_polynomial_dual (η : AddChar (v.adicCompletion ℚ) ℂ) (hη : η ≠ 1) (W : LocalGL3 v → ℂ)
    (hW : IsGL3PsiWhittakerFn η W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v) (σ₁ : ℝ) :
    letI := localBorel ℚ v
    IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        (dualWhittakerFn3 W) τ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ →
      ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ ∀ s : ℂ, σ₁ < (1 - s).re →
        Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
            localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W τ
              (1 - s) g =
          P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
  letI := localBorel ℚ v
  intro h31
  have hWd : IsGL3PsiWhittakerFn η⁻¹ (dualWhittakerFn3 W) :=
    LanglandsTunnell.CubicInduction.isGL3PsiWhittakerFn_dualWhittakerFn3 η W hW
  have hηinv : ∃ y₀ : v.adicCompletion ℚ, η⁻¹ y₀ ≠ 1 := by
    obtain ⟨y₀, hy₀⟩ := AddChar.ne_one_iff.mp hη
    exact ⟨-y₀, by rw [AddChar.inv_apply, neg_neg]; exact hy₀⟩
  have hsmd := smooth_dualWhittakerFn3 v hsm
  obtain ⟨Vd, hVdmem, hVd⟩ :=
    exists_mem_gl3CyclicSubspace_integral_lowerUnipotent21_eq v hWd hηinv hsmd (weylPrime3 * transposeInv3 g)
  exact exists_polynomial_localZetaDual31 v η⁻¹ (AddChar.ne_one_iff.mpr hηinv) W τ g σ₁ Vd
    (isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace v hWd hVdmem) (smooth_of_mem_gl3CyclicSubspace v hsmd hVdmem)
    (admissible_of_gl3CyclicSubspace_le v (admissible_dualWhittakerFn3 v hadm) (gl3CyclicSubspace_le_of_mem v hVdmem))
    hVd h31

end DualInstance

end LocalZetaRational

end ZetaRationality

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

open LanglandsTunnell.CubicInduction

namespace TorusZ0

open Set
open scoped NNReal

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem diagUnitGL2_mem_localLevelOne_top (u : (v.adicCompletion ℚ)ˣ) (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    diagUnitGL2 u ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
  have hu' : Valued.v ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  have hinv : (diagUnitGL2 u)⁻¹ = diagUnitGL2 u⁻¹ := by
    rw [← diagHom_apply, ← diagHom_apply, map_inv]
  have key : ∀ (w : (v.adicCompletion ℚ)ˣ), Valued.v (w : v.adicCompletion ℚ) = 1 →
      AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ v ⊤ ((diagUnitGL2 w : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix _ _ _) := by
    intro w hw
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      fin_cases i <;> fin_cases j <;> simp [diagUnitGL2, hw]
    · rw [NumberField.AdelicLevel.idealBound_top]
      simp [diagUnitGL2]
    · rw [NumberField.AdelicLevel.idealBound_top]
      simp [diagUnitGL2]
  rw [AdelicDock.mem_localLevelOne_iff, hinv]
  exact ⟨key u hu, key u⁻¹ hu'⟩

theorem scalarPi_commute {K : Type*} [Field K] (π : K) (hπ : π ≠ 0) (g : GL (Fin 2) K) :
    Commute (scalarPi π hπ) g := by
  apply Units.ext
  show (scalarPi π hπ : Matrix (Fin 2) (Fin 2) K) * g = g * scalarPi π hπ
  have : (scalarPi π hπ : Matrix (Fin 2) (Fin 2) K) = π • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [scalarPi, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  rw [this, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

theorem diagUnitGL2_mk0_zpow {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) (j : ℤ) :
    diagUnitGL2 ((Units.mk0 _ hπ) ^ j) =
      diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ j := by
  apply Units.ext
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [diagUnitGL2, diagZ, Matrix.GeneralLinearGroup.mkOfDetNeZero, Units.val_zpow_eq_zpow_val]

end TorusZ0

open LocalZetaRational in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (W : LocalGL3 v → ℂ)
    (hWK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, W (g * iotaGL k) = W g)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (k : ℤ) (σ₀ : ℝ)
    (hconv : letI := localBorel ℚ v
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1
        (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k)) σ₀)
    (s : ℂ) (hs : σ₀ < s.re) :
    letI := localBorel ℚ v
    HasSum
      (fun j : ℤ =>
        (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
              {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1}).toReal : ℂ) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-((j : ℂ) * (s - 1))) *
          W (iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ j *
            scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k)))
      (localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s
        (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k))) := by
  letI := localBorel ℚ v
  classical
  set ϖK : (v.adicCompletion ℚ)ˣ := Units.mk0 _ hπ with hϖK
  set g : LocalGL3 v := iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k)
    with hg

  have hint : Integrable (LocalZetaRational.zetaFn v W 1 s g)
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := hconv s hs
  have hsum := LocalZetaRational.hasSum_shellCoeff_mul_shellVar_zpow v W 1 s g hint

  have hvol : (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1}).toReal : ℂ) =
      (((selfDualHaarAt ℚ v) (LocalZetaRational.valShell v 0)).toReal : ℂ) := by
    have hset : {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1} =
        (Units.val ⁻¹' LocalZetaRational.valShell v 0 : Set (v.adicCompletion ℚ)ˣ) := by
      ext u
      simp [LocalZetaRational.mem_valShell]
    have h := LocalZetaRational.setIntegral_units_valShell v (fun _ => (1 : ℂ)) 0
    rw [zpow_zero, one_smul, setIntegral_const, setIntegral_const, Complex.real_smul, Complex.real_smul, mul_one,
      mul_one] at h
    rw [hset, ← measureReal_def, ← measureReal_def]
    exact h

  have hcoeff : ∀ j : ℤ, LocalZetaRational.shellCoeff v W 1 g j =
      (((selfDualHaarAt ℚ v) (LocalZetaRational.valShell v 0)).toReal : ℂ) *
        W (iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ j *
          scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k)) := by
    intro j
    rw [LocalZetaRational.shellCoeff, ← Complex.real_smul, ← measureReal_def, ← setIntegral_const]
    refine setIntegral_congr_fun (LocalZetaRational.measurableSet_valShell v 0) fun x hx => ?_
    have hx0 : x ≠ 0 := LocalZetaRational.ne_zero_of_mem_valShell v hx
    have hx1 : Valued.v x = 1 := by
      rw [(LocalZetaRational.mem_valShell v).mp hx, neg_zero, WithZero.exp_zero]
    rw [LocalZetaRational.torusFn_of_ne_zero v _ hx0, MonoidHom.one_apply, Units.val_one, mul_one]

    set u : (v.adicCompletion ℚ)ˣ := ϖK ^ (-j) * (AdelicLevel.uniformizerUnit ℚ v ^ j * Units.mk0 x hx0) with hu
    have hdec : AdelicLevel.uniformizerUnit ℚ v ^ j * Units.mk0 x hx0 = ϖK ^ j * u := by
      rw [hu, ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
    have hu1 : Valued.v (u : v.adicCompletion ℚ) = 1 := by
      have hval : Valued.v (u : v.adicCompletion ℚ) =
          Valued.v ((ϖK : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ^ (-j) *
            (Valued.v ((AdelicLevel.uniformizerUnit ℚ v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ^ j *
              Valued.v x) := by
        rw [hu]
        simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0]
      rw [hval, hx1, mul_one, hϖK, Units.val_mk0, hϖ, AdelicLevel.valued_uniformizerUnit, zpow_neg,
        inv_mul_cancel₀ (zpow_ne_zero j WithZero.exp_ne_zero)]
    have hK : diagUnitGL2 u ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ :=
      TorusZ0.diagUnitGL2_mem_localLevelOne_top v u hu1
    have hcomm : iotaGL (diagUnitGL2 u) * g = g * iotaGL (diagUnitGL2 u) := by
      rw [hg, ← map_mul, ← map_mul]
      congr 1
      exact ((TorusZ0.scalarPi_commute _ hπ (diagUnitGL2 u)).zpow_left k).symm.eq
    rw [hdec, LocalZetaRational.iotaGL_diagUnitGL2_mul, mul_assoc, hcomm, ← mul_assoc, hWK _ hK,
      hϖK, TorusZ0.diagUnitGL2_mk0_zpow v hπ j, ← map_mul]

  have hvar : ∀ j : ℤ, LocalZetaRational.shellVar v 1 s ^ j =
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-((j : ℂ) * (s - 1))) := by
    intro j
    have harg : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]; exact Real.pi_pos.ne
    rw [LocalZetaRational.shellVar, MonoidHom.one_apply, Units.val_one, one_mul, Complex.inv_cpow _ _ harg,
      ← Complex.cpow_neg, ← Complex.cpow_int_mul]
    congr 1
    ring
  convert hsum using 1
  funext j
  rw [hcoeff j, hvar j, hvol]
  ring

end S_LanglandsTunnell_CubicInduction_hasSum_shell_localZeta30_one_iotaGL_scalarPi_zpow_of_iotaGL_invariant
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_hasSum_shell_localZeta30_one_iotaGL_scalarPi_zpow_of_iotaGL_invariant (solution)
