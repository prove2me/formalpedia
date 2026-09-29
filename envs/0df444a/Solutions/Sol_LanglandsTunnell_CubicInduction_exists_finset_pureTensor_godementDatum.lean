-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_finset_pureTensor_godementDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/89a08d78-1a57-5cf5-b4e6-0adb68b24086

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

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Theorems.Thm_IsLocallyConstant_exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport
import Theorems.Thm_LanglandsTunnell_CubicInduction_godementDatum_mem_principalSeries2_and_support
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_pureTensor_godementDatum
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace B1ejf

variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => HeightOneSpectrum.adicCompletion ℚ p
local notation "Mx" => Matrix (Fin 2) (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p)

def ball (n : ℕ) : Set F := {x | Valued.v x ≤ WithZero.exp (-(n : ℤ))}

theorem zero_mem_ball (n : ℕ) : (0 : F) ∈ ball p n := by simp [ball]

theorem sub_mem_ball {n : ℕ} {x y : F} (hx : x ∈ ball p n) (hy : y ∈ ball p n) : x - y ∈ ball p n := by
  simp only [ball, Set.mem_setOf_eq] at hx hy ⊢
  exact (Valuation.map_sub _ x y).trans (max_le hx hy)

theorem neg_mem_ball {n : ℕ} {x : F} (hx : x ∈ ball p n) : -x ∈ ball p n := by
  simpa using sub_mem_ball p (zero_mem_ball p n) hx

theorem add_mem_ball {n : ℕ} {x y : F} (hx : x ∈ ball p n) (hy : y ∈ ball p n) : x + y ∈ ball p n := by
  simpa using sub_mem_ball p hx (neg_mem_ball p hy)

def coset (n : ℕ) (X₀ : Mx) : Set Mx := {X | ∀ i j, X i j - X₀ i j ∈ ball p n}

theorem mem_coset_self (n : ℕ) (X₀ : Mx) : X₀ ∈ coset p n X₀ := by
  intro i j; simp [zero_mem_ball]

theorem coset_eq_of_mem {n : ℕ} {X₀ X₁ X : Mx} (h₀ : X ∈ coset p n X₀) (h₁ : X ∈ coset p n X₁) :
    coset p n X₀ = coset p n X₁ := by
  ext Y
  constructor
  · intro hY i j
    have : Y i j - X₁ i j = (Y i j - X₀ i j) - (X i j - X₀ i j) + (X i j - X₁ i j) := by ring
    rw [this]; exact add_mem_ball p (sub_mem_ball p (hY i j) (h₀ i j)) (h₁ i j)
  · intro hY i j
    have : Y i j - X₀ i j = (Y i j - X₁ i j) - (X i j - X₁ i j) + (X i j - X₀ i j) := by ring
    rw [this]; exact add_mem_ball p (sub_mem_ball p (hY i j) (h₁ i j)) (h₀ i j)

theorem isOpen_coset (n : ℕ) (X₀ : Mx) : IsOpen (coset p n X₀) := by
  have : coset p n X₀ = ⋂ i : Fin 2, ⋂ j : Fin 3, (fun X : Mx => X i j) ⁻¹' {x | Valued.v (x - X₀ i j) ≤ WithZero.exp (-(n : ℤ))} := by
    ext X; simp [coset, ball]
  rw [this]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (isClopen_setOf_valued_sub_le p (X₀ i j) n).isOpen.preimage ((Continuous.matrix_elem continuous_id i j))

def boxU (n : ℕ) (X₀ : Mx) : Set (Matrix (Fin 2) (Fin 2) F) :=
  {M | ∀ (i : Fin 2) (j : Fin 2), Valued.v (M i j - X₀ i (Fin.castSucc j)) ≤ WithZero.exp (-(n : ℤ))}

def boxV (n : ℕ) (X₀ : Mx) : Set (F × F) :=
  {u | Valued.v (u.1 - X₀ 0 2) ≤ WithZero.exp (-(n : ℤ)) ∧ Valued.v (u.2 - X₀ 1 2) ≤ WithZero.exp (-(n : ℤ))}

theorem mem_coset_iff (n : ℕ) (X₀ X : Mx) :
    X ∈ coset p n X₀ ↔ (Matrix.of fun a b => X a (Fin.castSucc b)) ∈ boxU p n X₀ ∧ (X 0 2, X 1 2) ∈ boxV p n X₀ := by
  simp only [coset, ball, boxU, boxV, Set.mem_setOf_eq, Matrix.of_apply]
  constructor
  · intro h
    exact ⟨fun i j => h i _, h 0 2, h 1 2⟩
  · rintro ⟨hU, h0, h1⟩ i j
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · fin_cases i
      · exact h0
      · exact h1
    · exact hU i j'

theorem isClopen_boxU (n : ℕ) (X₀ : Mx) : IsClopen (boxU p n X₀) := by
  have : boxU p n X₀ = ⋂ i : Fin 2, ⋂ j : Fin 2, (fun M : Matrix (Fin 2) (Fin 2) F => M i j) ⁻¹'
      {x | Valued.v (x - X₀ i (Fin.castSucc j)) ≤ WithZero.exp (-(n : ℤ))} := by
    ext M; simp [boxU]
  rw [this]
  refine isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j => ?_
  exact (isClopen_setOf_valued_sub_le p _ n).preimage (Continuous.matrix_elem continuous_id i j)

theorem isCompact_boxU (n : ℕ) (X₀ : Mx) : IsCompact (boxU p n X₀) := by
  have : boxU p n X₀ = Set.pi Set.univ (fun i : Fin 2 => Set.pi Set.univ (fun j : Fin 2 =>
      {x : F | Valued.v (x - X₀ i (Fin.castSucc j)) ≤ WithZero.exp (-(n : ℤ))})) := by
    ext M
    simp only [boxU, Set.mem_setOf_eq]
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ i) j (Set.mem_univ j)⟩
  rw [this]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_setOf_valued_sub_le p _ n

theorem isClopen_boxV (n : ℕ) (X₀ : Mx) : IsClopen (boxV p n X₀) := by
  have : boxV p n X₀ = {x : F | Valued.v (x - X₀ 0 2) ≤ WithZero.exp (-(n : ℤ))} ×ˢ
      {x : F | Valued.v (x - X₀ 1 2) ≤ WithZero.exp (-(n : ℤ))} := by
    ext u; simp [boxV]
  rw [this]
  exact (isClopen_setOf_valued_sub_le p _ n).prod (isClopen_setOf_valued_sub_le p _ n)

theorem isCompact_boxV (n : ℕ) (X₀ : Mx) : IsCompact (boxV p n X₀) := by
  have : boxV p n X₀ = {x : F | Valued.v (x - X₀ 0 2) ≤ WithZero.exp (-(n : ℤ))} ×ˢ
      {x : F | Valued.v (x - X₀ 1 2) ≤ WithZero.exp (-(n : ℤ))} := by
    ext u; simp [boxV]
  rw [this]
  exact (isCompact_setOf_valued_sub_le p _ n).prod (isCompact_setOf_valued_sub_le p _ n)

theorem isLocallyConstant_indicator_one {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClopen S) :
    IsLocallyConstant (S.indicator fun _ => (1 : ℂ)) := by
  intro s
  classical
  by_cases h1 : (1 : ℂ) ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s
  · have : (S.indicator fun _ => (1 : ℂ)) ⁻¹' s = Set.univ := by
      ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]
    rw [this]; exact isOpen_univ
  · have : (S.indicator fun _ => (1 : ℂ)) ⁻¹' s = S := by
      ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]
    rw [this]; exact hS.isOpen
  · have : (S.indicator fun _ => (1 : ℂ)) ⁻¹' s = Sᶜ := by
      ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]
    rw [this]; exact hS.compl.isOpen
  · have : (S.indicator fun _ => (1 : ℂ)) ⁻¹' s = ∅ := by
      ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]
    rw [this]; exact isOpen_empty

theorem hasCompactSupport_indicator_one {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsCompact S) (hS' : IsClosed S) :
    HasCompactSupport (S.indicator fun _ => (1 : ℂ)) :=
  HasCompactSupport.intro' hS hS' fun x hx => Set.indicator_of_notMem hx _

theorem ball_mono {n m : ℕ} (h : n ≤ m) : ball p m ⊆ ball p n := by
  intro x hx
  simp only [ball, Set.mem_setOf_eq] at hx ⊢
  exact hx.trans (WithZero.exp_le_exp.mpr (by omega))

theorem exists_ball_subset_of_mem_nhds {s : Set F} (hs : s ∈ nhds (0 : F)) : ∃ n : ℕ, ball p n ⊆ s := by
  have hball : ∀ k : ℕ, ball p k = {x : F | Valued.v (x - 0) ≤ WithZero.exp (-(k : ℤ))} := by
    intro k; simp [ball]
  have hdir : Directed (· ⊇ ·) (fun k : ℕ => ball p k) := by
    intro a b
    exact ⟨max a b, ball_mono p (le_max_left a b), ball_mono p (le_max_right a b)⟩
  have hcpt : ∀ k : ℕ, IsCompact (ball p k) := fun k => by rw [hball]; exact isCompact_setOf_valued_sub_le p 0 k
  have hcl : ∀ k : ℕ, IsClosed (ball p k) := fun k => by rw [hball]; exact (isClopen_setOf_valued_sub_le p 0 k).isClosed
  have hinter : ∀ x ∈ ⋂ k : ℕ, ball p k, x = (0 : F) := by
    intro x hx
    by_contra hx0
    have hv0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
    set m : ℤ := WithZero.log (Valued.v x) with hm
    have hvm : Valued.v x = WithZero.exp m := by rw [hm, WithZero.exp_log hv0]
    have := Set.mem_iInter.mp hx (m.natAbs + 1)
    simp only [ball, Set.mem_setOf_eq, hvm, WithZero.exp_le_exp] at this
    omega
  exact exists_subset_nhds_of_isCompact hdir hcpt (fun x hx => by rw [hinter x hx]; exact hs)

theorem exists_box_subset {s : Set Mx} (hs : s ∈ nhds (0 : Mx)) :
    ∃ n : ℕ, ∀ b : Mx, (∀ i j, b i j ∈ ball p n) → b ∈ s := by
  classical
  have hs' : s ∈ Filter.pi fun i : Fin 2 => nhds ((0 : Mx) i) := by rwa [← nhds_pi]
  obtain ⟨I, -, t1, ht1, hsub1⟩ := Filter.mem_pi.mp hs'
  have h2 : ∀ i : Fin 2, ∃ t2 : Fin 3 → Set F, (∀ j, t2 j ∈ nhds (0 : F)) ∧ Set.pi Set.univ t2 ⊆ t1 i := by
    intro i
    have : t1 i ∈ Filter.pi fun j : Fin 3 => nhds ((0 : Mx) i j) := by rw [← nhds_pi]; exact ht1 i
    obtain ⟨J, -, t2, ht2, hsub2⟩ := Filter.mem_pi.mp this
    exact ⟨t2, ht2, fun x hx => hsub2 fun j _ => hx j (Set.mem_univ j)⟩
  choose t2 ht2 hsub2 using h2
  have h3 : ∀ i j, ∃ n : ℕ, ball p n ⊆ t2 i j := fun i j => exists_ball_subset_of_mem_nhds p (ht2 i j)
  choose nf hnf using h3
  refine ⟨∑ i, ∑ j, nf i j, fun b hb => hsub1 fun i _ => hsub2 i fun j _ => hnf i j (ball_mono p ?_ (hb i j))⟩
  exact (Finset.single_le_sum (f := fun j => nf i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, nf i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))

end B1ejf

open B1ejf in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (T : LocalGL3 p) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) → IsCompact (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
    ∀ (φsec : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) → GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (φsec = fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)) =>
        let Z : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) := X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))
        let s : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) := Matrix.of fun i j => Z i (Fin.castSucc j)
        let N : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) := (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * Z
        ((μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ)⁻¹ *
          (((lam 0 (Matrix.GeneralLinearGroup.det T) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det T : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)) *
          (Units.val '' (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).indicator (fun _ => (1 : ℂ)) s *
          (charExt (lam 0) s.det)⁻¹ * ((‖s.det‖⁻¹ : ℝ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
              ^ (1 / 2 : ℂ) *
          charExt (lam 1) (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * s.det / N 1 0) *
          charExt (lam 2) (N 1 0) * ((‖N 1 0‖⁻¹ : ℝ) : ℂ) *
          Φ ![N 1 1 / N 1 0, N 1 2 / N 1 0, (Z 0 0 * Z 1 2 - Z 0 2 * Z 1 0) / s.det]) →
    ∃ (m : ℕ) (φ₁ : Fin m → Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ)
        (φ₂ : Fin m → (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ)
        (φ : Fin m → GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ i, IsLocallyConstant (φ₁ i) ∧ HasCompactSupport (φ₁ i)) ∧
      (∀ i, IsLocallyConstant (φ₂ i) ∧ HasCompactSupport (φ₂ i)) ∧
      (∀ i, φ i ∈ principalSeries2 p ![lam 1, lam 2] ∧
        ∃ s ∈ K, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), φ i g ≠ 0 →
          ((g * s : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 ≠ 0) ∧
      (∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        φsec X g = ∑ i, φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) * φ i g) ∧
      (∀ (i : Fin m) (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        ‖φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) * φ i g‖ ≤ ‖φsec X g‖) := by
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  letI : MeasurableSpace (Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) := borel _
  intro μ₂ _ K hKo hKc φsec hφ
  classical
  obtain ⟨U, R, hUo, hU1, hmain⟩ :=
    LanglandsTunnell.CubicInduction.godementDatum_mem_principalSeries2_and_support p lam hlam Φ hΦ T
  obtain ⟨-, hlc, hcs, hsK, hPS, -⟩ := hmain μ₂ K hKo hKc φsec hφ

  obtain ⟨W, hWo, hW1, hW⟩ :=
    IsLocallyConstant.exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport
      (G := Multiplicative (Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)))
      (fun X => φsec (Multiplicative.toAdd X)) hlc hcs
  have hinvW : ∀ X b : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ), Multiplicative.ofAdd b ∈ W → φsec (X + b) = φsec X :=
    fun X b hb => (hW (Multiplicative.ofAdd X) (Multiplicative.ofAdd b) hb).1

  have hWn : {b : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) | Multiplicative.ofAdd b ∈ W} ∈
      nhds (0 : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) :=
    (continuous_ofAdd.isOpen_preimage W hWo).mem_nhds hW1
  obtain ⟨n, hn⟩ := exists_box_subset p hWn
  have hcos : ∀ X₀ X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ), X ∈ coset p n X₀ → φsec X = φsec X₀ := by
    intro X₀ X hX
    have := hinvW X₀ (X - X₀) (hn _ fun i j => by have h__af := hX i j; simp at h__af ⊢; exact h__af)
    rwa [add_sub_cancel] at this

  obtain ⟨t, ht⟩ := hcs.elim_finite_subcover (fun X₀ => coset p n X₀) (fun X₀ => isOpen_coset p n X₀)
    (fun X _ => Set.mem_iUnion.mpr ⟨X, mem_coset_self p n X⟩)
  set C : Finset (Set (Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ))) := t.image (coset p n) with hC
  have hrepex : ∀ c : C, ∃ X₀ ∈ t, coset p n X₀ = (c : Set _) := fun c => Finset.mem_image.mp c.2
  choose rep hrept hrep using hrepex
  set m : ℕ := C.card with hm
  set e : C ≃ Fin m := C.equivFin with he
  set Xr : Fin m → Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) := fun i => rep (e.symm i) with hXr
  have hXr : ∀ i, coset p n (Xr i) = ((e.symm i : C) : Set _) := fun i => hrep _

  have huniq : ∀ (i j : Fin m) (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)),
      X ∈ coset p n (Xr i) → X ∈ coset p n (Xr j) → i = j := by
    intro i j X hi hj
    have h1 : coset p n (Xr i) = coset p n (Xr j) := coset_eq_of_mem p hi hj
    rw [hXr, hXr] at h1
    have h2 : e.symm i = e.symm j := Subtype.ext h1
    exact e.symm.injective h2

  let φ₁ : Fin m → Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ := fun i => (boxU p n (Xr i)).indicator fun _ => 1
  let φ₂ : Fin m → (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ := fun i => (boxV p n (Xr i)).indicator fun _ => 1
  let φ : Fin m → GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun i => φsec (Xr i)
  have hprod : ∀ (i : Fin m) (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)),
      φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) =
        if X ∈ coset p n (Xr i) then 1 else 0 := by
    intro i X
    by_cases hX : X ∈ coset p n (Xr i)
    · obtain ⟨hU, hV⟩ := (mem_coset_iff p n (Xr i) X).mp hX
      simp [φ₁, φ₂, Set.indicator_of_mem hU, Set.indicator_of_mem hV, hX]
    · rw [if_neg hX]
      rw [mem_coset_iff] at hX
      push Not at hX
      by_cases hU : (Matrix.of fun a b => X a (Fin.castSucc b)) ∈ boxU p n (Xr i)
      · simp [φ₁, φ₂, Set.indicator_of_notMem (hX hU)]
      · simp [φ₁, Set.indicator_of_notMem hU]
  refine ⟨m, φ₁, φ₂, φ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨isLocallyConstant_indicator_one (isClopen_boxU p n (Xr i)),
      hasCompactSupport_indicator_one (isCompact_boxU p n (Xr i)) (isClopen_boxU p n (Xr i)).isClosed⟩
  · intro i
    exact ⟨isLocallyConstant_indicator_one (isClopen_boxV p n (Xr i)),
      hasCompactSupport_indicator_one (isCompact_boxV p n (Xr i)) (isClopen_boxV p n (Xr i)).isClosed⟩
  · intro i
    refine ⟨(hPS (Xr i)).1, ?_⟩
    by_cases hex : ∃ g₀ : GL (Fin 2) (p.adicCompletion ℚ), φsec (Xr i) g₀ ≠ 0
    · obtain ⟨g₀, hg₀⟩ := hex
      obtain ⟨k, hk, hkeq⟩ := hsK (Xr i) g₀ hg₀
      refine ⟨k, hk, fun g hg => ?_⟩
      have := ((hPS (Xr i)).2 g hg).1
      rwa [Units.val_mul, hkeq]
    · push Not at hex
      exact ⟨1, K.one_mem, fun g hg => absurd (hex g) hg⟩
  · intro X g
    simp only [φ]
    have hsum : (∑ i, φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) * φsec (Xr i) g) =
        ∑ i, (if X ∈ coset p n (Xr i) then 1 else 0) * φsec (Xr i) g := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hprod]
    rw [hsum]
    by_cases hex : ∃ i, X ∈ coset p n (Xr i)
    · obtain ⟨i, hi⟩ := hex
      rw [Finset.sum_eq_single i]
      · rw [if_pos hi, one_mul, hcos _ _ hi]
      · intro j _ hji
        rw [if_neg, zero_mul]
        intro hj
        exact hji (huniq j i X hj hi)
      · intro h; exact absurd (Finset.mem_univ i) h
    · push Not at hex
      have hzero : φsec X = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hX
        obtain ⟨X₀, hX₀⟩ := Set.mem_iUnion.mp (ht hX)
        obtain ⟨hX₀t, hXc⟩ := Set.mem_iUnion.mp hX₀
        have hc : coset p n X₀ ∈ C := Finset.mem_image.mpr ⟨X₀, hX₀t, rfl⟩
        have := hex (e ⟨coset p n X₀, hc⟩)
        rw [hXr, Equiv.symm_apply_apply] at this
        exact this hXc
      rw [hzero, Pi.zero_apply]
      symm
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg (hex i), zero_mul]
  · intro i X g
    simp only [φ]
    rw [show φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) * φsec (Xr i) g =
      (if X ∈ coset p n (Xr i) then 1 else 0) * φsec (Xr i) g from by rw [hprod]]
    by_cases hX : X ∈ coset p n (Xr i)
    · rw [if_pos hX, one_mul, hcos _ _ hX]
    · rw [if_neg hX, zero_mul, norm_zero]; exact norm_nonneg _

end

end S_LanglandsTunnell_CubicInduction_exists_finset_pureTensor_godementDatum
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_pureTensor_godementDatum (solution)
