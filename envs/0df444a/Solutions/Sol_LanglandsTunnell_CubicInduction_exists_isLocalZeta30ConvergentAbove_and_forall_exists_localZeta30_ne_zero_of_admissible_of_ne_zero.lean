-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_isLocalZeta30ConvergentAbove_and_forall_exists_localZeta30_ne_zero_of_admissible_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ced96cf0-8755-5eaa-8366-1b116b29e278

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Theorems.Thm_LanglandsTunnell_CubicInduction_setIntegral_valuationShell_eq_zero_of_forall_integral_mul_modulus_cpow_eq_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_apply_iotaGL_diagUnitGL2_mul_upperUnipotent3_mul_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_forall_setIntegral_valuationShell_addChar_mul_eq_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_diagUnitGL2_mul_eq_zero_of_lt_valued_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_polynomial_mul_localZeta30_eq_and_dual_of_isGL3PsiWhittakerFn
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isLocalZeta30ConvergentAbove_and_forall_exists_localZeta30_ne_zero_of_admissible_of_ne_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory

namespace Ws31
namespace NonvanAsm

theorem eventually_eval_natCast_cpow_neg_ne_zero (Q : Polynomial ℂ) (hQ : Q ≠ 0) (N : ℕ) (hN : 1 < N) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Q.eval ((N : ℂ) ^ (-s)) ≠ 0 := by
  classical
  have hN0 : 0 < N := lt_trans Nat.zero_lt_one hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  refine ⟨(∑ r ∈ Q.roots.toFinset, |Real.log ‖r‖|) / Real.log (N : ℝ), fun s hs h => ?_⟩
  have hmem : ((N : ℂ) ^ (-s)) ∈ Q.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ]; exact h
  have hnorm : ‖(N : ℂ) ^ (-s)‖ = (N : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hN0]; simp
  have hlog : Real.log ‖(N : ℂ) ^ (-s)‖ = -s.re * Real.log (N : ℝ) := by
    rw [hnorm, Real.log_rpow (by exact_mod_cast hN0)]
  have hle : |Real.log ‖(N : ℂ) ^ (-s)‖| ≤ ∑ r ∈ Q.roots.toFinset, |Real.log ‖r‖| :=
    Finset.single_le_sum (f := fun r : ℂ => |Real.log ‖r‖|) (fun _ _ => abs_nonneg _) hmem
  rw [hlog] at hle
  have hσ0 : 0 ≤ (∑ r ∈ Q.roots.toFinset, |Real.log ‖r‖|) / Real.log (N : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) hlogN.le
  have hspos : 0 < s.re := lt_of_le_of_lt hσ0 hs
  have habs : |(-s.re) * Real.log (N : ℝ)| = s.re * Real.log (N : ℝ) := by
    rw [abs_of_nonpos (by nlinarith)]; ring
  rw [habs] at hle
  have := (div_lt_iff₀ hlogN).mp hs
  linarith

end Ws31.NonvanAsm

section QuarryInfra
open NumberField.TateGlobal

namespace LocalZetaRational

variable (v : HeightOneSpectrum (𝓞 ℚ))

def EntriesLE (A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (e : WithZero (Multiplicative ℤ)) : Prop :=
  ∀ i j, Valued.v (A i j) ≤ e

theorem entriesLE_mul {A B : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {x y : WithZero (Multiplicative ℤ)}
    (hA : EntriesLE v A x) (hB : EntriesLE v B y) : EntriesLE v (A * B) (x * y) := by
  intro i j
  have hterm : ∀ l, Valued.v (A i l * B l j) ≤ x * y := fun l => by
    rw [Valuation.map_mul]
    exact mul_le_mul' (hA i l) (hB l j)
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

theorem entriesLE_add {A B : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {e : WithZero (Multiplicative ℤ)}
    (hA : EntriesLE v A e) (hB : EntriesLE v B e) : EntriesLE v (A + B) e := fun i j => by
  rw [Matrix.add_apply]
  exact le_trans (Valuation.map_add _ _ _) (max_le (hA i j) (hB i j))

theorem entriesLE_neg {A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {e : WithZero (Multiplicative ℤ)}
    (hA : EntriesLE v A e) : EntriesLE v (-A) e := fun i j => by
  rw [Matrix.neg_apply, Valuation.map_neg]
  exact hA i j

theorem entriesLE_mono {A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {e e' : WithZero (Multiplicative ℤ)}
    (h : e ≤ e') (hA : EntriesLE v A e) : EntriesLE v A e' := fun i j => (hA i j).trans h

theorem entriesLE_one_of_mem {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    EntriesLE v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 ∧
      EntriesLE v ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 :=
  (mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hk

def principalCongruence3 (m : ℕ) : Subgroup (LocalGL3 v) where
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

theorem mem_principalCongruence3_iff {m : ℕ} {k : LocalGL3 v} :
    k ∈ principalCongruence3 v m ↔ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧
      EntriesLE v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) (WithZero.exp (-(m : ℤ))) :=
  Iff.rfl

theorem principalCongruence3_le_localMaximalCompact3 (m : ℕ) :
    principalCongruence3 v m ≤ localMaximalCompact3 (𝓞 ℚ) ℚ v := fun _ hk => hk.1

theorem principalCongruence3_antitone {m m' : ℕ} (h : m ≤ m') :
    principalCongruence3 v m' ≤ principalCongruence3 v m := fun _ hk =>
  ⟨hk.1, entriesLE_mono v (WithZero.exp_le_exp.mpr (by omega)) hk.2⟩

theorem conj_mem_principalCongruence3 {m : ℕ} {k g : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
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

theorem isOpen_setOf_forall_entry_mem {S : Set (v.adicCompletion ℚ)} (hS : IsOpen S) :
    IsOpen {A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) | ∀ i j, A i j ∈ S} := by
  have h : {A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) | ∀ i j, A i j ∈ S} =
      ⋂ i, ⋂ j, (fun A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) => A i j) ⁻¹' S := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hS.preimage (continuous_id.matrix_elem i j)

theorem exists_setOf_forall_entry_sub_le_subset_of_isOpen
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

theorem isOpen_principalCongruence3 (m : ℕ) : IsOpen (principalCongruence3 v m : Set (LocalGL3 v)) := by
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
  convert (h1.inter h2).inter h3 using 1 <;> try first | rfl | ext; simp [principalCongruence3]

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

theorem exists_level_of_smooth {W : LocalGL3 v → ℂ}
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ u ∈ Uv, ∀ g, W (g * u) = W g) :
    ∃ m : ℕ, ∀ u ∈ principalCongruence3 v m, ∀ g, W (g * u) = W g := by
  obtain ⟨Uv, hUo, hUW⟩ := hsm
  obtain ⟨m, hm⟩ := exists_principalCongruence3_le_of_isOpen v Uv hUo
  exact ⟨m, fun u hu g => hUW u (hm hu) g⟩

theorem coe_iotaGL_diagUnitGL2 (u : (v.adicCompletion ℚ)ˣ) :
    ((iotaGL (diagUnitGL2 u) : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![(u : v.adicCompletion ℚ), 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, diagUnitGL2]

end LocalZetaRational

end QuarryInfra

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

set_option maxHeartbeats 4000000 in
theorem solution
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (v : HeightOneSpectrum (𝓞 ℚ)) (hψv : psiLoc ψ v ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn (psiLoc ψ v) W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hωv : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1)
    (hcen : ∀ (z : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ωv z : ℂˣ) : ℂ) * W g)
    (hW0 : W ≠ 0)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : ∃ c : ℕ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v χ c) :
    letI := localBorel ℚ v
    ∃ (g : LocalGL3 v) (σ₀ : ℝ),
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ g σ₀ ∧
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s g ≠ 0 := by
  letI := localBorel ℚ v
  have hN1 : 1 < Ideal.absNorm v.asIdeal := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    omega

  obtain ⟨σ₀, σ₁, hloc⟩ :=
    LanglandsTunnell.CubicInduction.exists_polynomial_mul_localZeta30_eq_and_dual_of_isGL3PsiWhittakerFn ψ v hψv W hW
      hsm hadm ωv hωv hcen χ hχ
  have hconv := fun g => (hloc g).1.1
  have h1 := fun g => (hloc g).1.2
  choose P Q hQ hP using h1

  suffices hex : ∃ g, P g ≠ 0 by
    obtain ⟨g, hPg⟩ := hex
    refine ⟨g, σ₀, hconv g, fun σ => ?_⟩
    obtain ⟨σQ, hσQ⟩ := Ws31.NonvanAsm.eventually_eval_natCast_cpow_neg_ne_zero (P g * Q g) (mul_ne_zero hPg (hQ g)) _ hN1
    set s : ℂ := ((max (max σ σ₀) σQ + 1 : ℝ) : ℂ) with hs
    have hsre : s.re = max (max σ σ₀) σQ + 1 := by simp [hs]
    refine ⟨s, by rw [hsre]; exact lt_of_le_of_lt (le_max_left _ _ |>.trans (le_max_left _ _)) (lt_add_one _), ?_⟩
    intro hZ
    have h := hP g s (by rw [hsre]; exact lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) (lt_add_one _))
    have hPQ := hσQ s (by rw [hsre]; exact lt_of_le_of_lt (le_max_right _ _) (lt_add_one _))
    rw [hZ, mul_zero] at h
    rw [Polynomial.eval_mul] at hPQ
    exact hPQ (by rw [← h]; ring)
  by_contra hall
  simp only [not_exists, not_not] at hall

  have hZ0 : ∀ g : LocalGL3 v, ∃ σ' : ℝ, σ₀ ≤ σ' ∧ ∀ s : ℂ, σ' < s.re →
      localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s g = 0 := by
    intro g
    obtain ⟨σQ, hσQ⟩ := Ws31.NonvanAsm.eventually_eval_natCast_cpow_neg_ne_zero (Q g) (hQ g) _ hN1
    refine ⟨max σ₀ σQ, le_max_left _ _, fun s hs => ?_⟩
    have h := hP g s (lt_of_le_of_lt (le_max_left _ _) hs)
    rw [hall g, Polynomial.eval_zero] at h
    rcases mul_eq_zero.mp h with hq | hz
    · exact absurd hq (hσQ s (lt_of_le_of_lt (le_max_right _ _) hs))
    · exact hz

  have hshell : ∀ (g : LocalGL3 v) (k : ℤ),
      ∫ a in {a : (v.adicCompletion ℚ)ˣ | Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (-k)},
        W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) = 0 := by
    intro g
    obtain ⟨σ', hσ', hz⟩ := hZ0 g
    obtain ⟨K, hK⟩ :=
      LanglandsTunnell.CubicInduction.exists_forall_apply_iotaGL_diagUnitGL2_mul_eq_zero_of_lt_valued_of_isGL3PsiWhittakerFn
        v (psiLoc ψ v) hψv W hW hsm g
    refine LanglandsTunnell.CubicInduction.setIntegral_valuationShell_eq_zero_of_forall_integral_mul_modulus_cpow_eq_zero v
      (fun a => W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ)) σ' K
      (fun a ha => by simp only [hK a ha, zero_mul]) (fun s hs => hconv g s (lt_of_le_of_lt hσ' hs)) (fun s hs => hz s hs)

  have htwist : ∀ (g : LocalGL3 v) (k : ℤ) (y : v.adicCompletion ℚ),
      ∫ a in {a : (v.adicCompletion ℚ)ˣ | Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (-k)},
        psiLoc ψ v (y * (a : v.adicCompletion ℚ)) * (W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ))
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) = 0 := by
    intro g k y
    have h := hshell (upperUnipotent3 y 0 0 * g) k
    rw [← h]
    congr 1; funext a
    rw [LanglandsTunnell.CubicInduction.apply_iotaGL_diagUnitGL2_mul_upperUnipotent3_mul_of_isGL3PsiWhittakerFn v (psiLoc ψ v)
      W hW a y g, mul_comm y]
    ring

  have hψloc : ∃ n : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → psiLoc ψ v x = 1 := by
    obtain ⟨g₀, hg₀⟩ : ∃ g₀, W g₀ ≠ 0 := by
      by_contra h; simp only [not_exists, not_not] at h; exact hW0 (funext h)
    obtain ⟨Uv, hUo, hUW⟩ := hsm

    let U' : Subgroup (LocalGL3 v) := Uv.map (MulAut.conj g₀).toMonoidHom
    have hU'o : IsOpen (U' : Set (LocalGL3 v)) := by
      have : (U' : Set (LocalGL3 v)) = (Homeomorph.mulLeft g₀).trans (Homeomorph.mulRight g₀⁻¹) '' (Uv : Set (LocalGL3 v)) := by
        ext k; simp [U', Subgroup.mem_map, MulAut.conj_apply]
      rw [this]; exact (Homeomorph.isOpenMap _) _ hUo
    obtain ⟨m, hm⟩ := LocalZetaRational.exists_principalCongruence3_le_of_isOpen v U' hU'o
    refine ⟨-(m : ℤ), fun x hx => ?_⟩

    have hn : (upperUnipotent3 x 0 0 : LocalGL3 v) ∈ LocalZetaRational.principalCongruence3 v m := by
      have hx1 : Valued.v x ≤ 1 := hx.trans (WithZero.exp_le_exp.mpr (by omega) |>.trans_eq WithZero.exp_zero)
      refine ⟨(mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mpr ⟨?_, ?_⟩, ?_⟩
      · intro i j
        fin_cases i <;> fin_cases j <;> (try simp) <;> first | exact hx1 | (simpa using hx1) | (simpa using hx)
      · intro i j
        change Valued.v ((upperUnipotent3 x 0 0 : LocalGL3 v).inv i j) ≤ 1
        fin_cases i <;> fin_cases j <;> (try simp [upperUnipotent3]) <;> first | exact hx1 | (simpa using hx1) | (simpa [Valuation.map_neg] using hx1) | (simpa using hx)
      · intro i j
        fin_cases i <;> fin_cases j <;> (try simp) <;> first | exact hx | (simpa using hx) | (simpa using hx1)
    have hmem : g₀⁻¹ * upperUnipotent3 x 0 0 * g₀ ∈ Uv := by
      have := hm hn
      simp only [U', Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      obtain ⟨k, hk, hkeq⟩ := this
      have : k = g₀⁻¹ * upperUnipotent3 x 0 0 * g₀ := by
        rw [← hkeq]; group
      rw [← this]; exact hk
    have h1 : W (upperUnipotent3 x 0 0 * g₀) = W g₀ := by
      have := hUW _ hmem g₀
      rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at this
    have h2 := hW x 0 0 g₀
    rw [h1, add_zero] at h2

    have := mul_right_cancel₀ hg₀ (h2.symm.trans (one_mul _).symm)
    exact this

  have hlc : ∀ (g : LocalGL3 v) (k : ℤ), ∃ m : ℕ, ∀ a b : (v.adicCompletion ℚ)ˣ,
      Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (-k) →
      Valued.v ((b : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-((m : ℤ) + 1)) →
      W (iotaGL (diagUnitGL2 (a * b)) * g) * ((χ (a * b) : ℂˣ) : ℂ) = W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) := by
    intro g k
    obtain ⟨Uv, hUo, hUW⟩ := hsm
    let U' : Subgroup (LocalGL3 v) := Uv.map (MulAut.conj g).toMonoidHom
    have hU'o : IsOpen (U' : Set (LocalGL3 v)) := by
      have : (U' : Set (LocalGL3 v)) = (Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹) '' (Uv : Set (LocalGL3 v)) := by
        ext k'; simp [U', MulAut.conj_apply]
      rw [this]; exact (Homeomorph.isOpenMap _) _ hUo
    obtain ⟨m₁, hm₁⟩ := LocalZetaRational.exists_principalCongruence3_le_of_isOpen v U' hU'o
    obtain ⟨c, hc⟩ := hχ
    refine ⟨max m₁ c, fun a b _ha hb => ?_⟩
    have hbm : Valued.v ((b : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(m₁ : ℤ)) :=
      hb.trans (WithZero.exp_le_exp.mpr (by push_cast; omega))
    have hb1 : Valued.v ((b : v.adicCompletion ℚ) - 1) < 1 := by
      refine lt_of_le_of_lt hb ?_
      rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by push_cast; omega)
    have hbv : Valued.v (b : v.adicCompletion ℚ) = 1 := by
      have := Valuation.map_one_add_of_lt (Valued.v) hb1
      rwa [add_sub_cancel] at this
    have hbvi : Valued.v ((b⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hbv, inv_one]
    have hdmul : ∀ a' b' : (v.adicCompletion ℚ)ˣ, diagUnitGL2 (a' * b') = diagUnitGL2 a' * diagUnitGL2 b' := by
      intro a' b'
      apply Units.ext
      simp only [diagUnitGL2, Units.val_mul]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hdinv : ∀ b' : (v.adicCompletion ℚ)ˣ, (diagUnitGL2 b')⁻¹ = diagUnitGL2 b'⁻¹ := by
      intro b'
      rw [inv_eq_iff_mul_eq_one, ← hdmul, mul_inv_cancel]
      apply Units.ext
      simp only [diagUnitGL2, Units.val_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp

    have hdb : (iotaGL (diagUnitGL2 b) : LocalGL3 v) ∈ LocalZetaRational.principalCongruence3 v m₁ := by
      refine ⟨(mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mpr ⟨?_, ?_⟩, ?_⟩
      · intro i j
        rw [LocalZetaRational.coe_iotaGL_diagUnitGL2]
        fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hbv]
      · intro i j
        rw [← map_inv, hdinv, LocalZetaRational.coe_iotaGL_diagUnitGL2]
        fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hbvi, hbv]
      · intro i j
        rw [LocalZetaRational.coe_iotaGL_diagUnitGL2]
        fin_cases i <;> fin_cases j <;> (try simp [Matrix.diagonal]) <;> first | exact hbm | (simpa using hbm)
    have hmem : g⁻¹ * iotaGL (diagUnitGL2 b) * g ∈ Uv := by
      have := hm₁ hdb
      simp only [U', Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      obtain ⟨k', hk', hkeq⟩ := this
      have : k' = g⁻¹ * iotaGL (diagUnitGL2 b) * g := by
        rw [← hkeq]; group
      rw [← this]; exact hk'
    have hW' : W (iotaGL (diagUnitGL2 (a * b)) * g) = W (iotaGL (diagUnitGL2 a) * g) := by
      have := hUW _ hmem (iotaGL (diagUnitGL2 a) * g)
      rw [show iotaGL (diagUnitGL2 a) * g * (g⁻¹ * iotaGL (diagUnitGL2 b) * g) =
        iotaGL (diagUnitGL2 (a * b)) * g by rw [hdmul, map_mul]; simp only [mul_assoc, mul_inv_cancel_left]] at this
      exact this
    have hχb : χ b = 1 := by
      refine hc.1 b ⟨hbv, ?_⟩
      rcases Nat.eq_zero_or_pos c with h0 | hpos
      · exact Or.inl h0
      · exact Or.inr (hb.trans (WithZero.exp_le_exp.mpr (by push_cast; omega)))
    rw [hW', map_mul, hχb, mul_one]

  have hvan : ∀ (g : LocalGL3 v) (a : (v.adicCompletion ℚ)ˣ), W (iotaGL (diagUnitGL2 a) * g) = 0 := by
    intro g a
    obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (-k) := by
      have ha : Valued.v (a : v.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).2 a.ne_zero
      exact ⟨-WithZero.log (Valued.v (a : v.adicCompletion ℚ)), by rw [neg_neg, WithZero.exp_log ha]⟩
    obtain ⟨m, hm⟩ := hlc g k
    have h := LanglandsTunnell.CubicInduction.eq_zero_of_forall_setIntegral_valuationShell_addChar_mul_eq_zero v (psiLoc ψ v) hψv
      hψloc k (fun a => W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ)) m hm (htwist g k) a hk
    rcases mul_eq_zero.mp h with hw | hc
    · exact hw
    · exact absurd hc (Units.ne_zero _)
  apply hW0
  funext g
  have := hvan ((iotaGL (diagUnitGL2 (1 : (v.adicCompletion ℚ)ˣ)))⁻¹ * g) 1
  rwa [mul_inv_cancel_left] at this

end S_LanglandsTunnell_CubicInduction_exists_isLocalZeta30ConvergentAbove_and_forall_exists_localZeta30_ne_zero_of_admissible_of_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_isLocalZeta30ConvergentAbove_and_forall_exists_localZeta30_ne_zero_of_admissible_of_ne_zero (solution)
