-- Prove2me | solution 1 for Hairer.pi_determined_by_gamma
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T06:34:34.040778+00:00
-- url     : https://prove2.me/submissions/ef9d8c6d-ed6b-4f1b-b89e-0b2d00aa68f6

import Definitions.Def_Hairer_Model
import Theorems.Thm_Hairer_reconstruction_uniqueness

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

open Hairer

/-- **Proposition 3.31, Hairer 2014.** -/
theorem solution
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi Pi' : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam) (hmod' : IsModel s r G Pi' Gam)
    {ν : ℝ} (hν : 0 < ν) (hνA : ν ∈ A)
    (hlow : ∀ (b : A), (b : ℝ) < ν → ∀ (a : E b), ∀ x : Pt d,
      Pi x (incl b a) = Pi' x (incl b a)) :
    ∀ (a : E (⟨ν, hνA⟩ : A)), ∀ x : Pt d,
      Pi x (incl (⟨ν, hνA⟩ : A) a) = Pi' x (incl (⟨ν, hνA⟩ : A) a) := by
  intro a x
  set u : ModelSpace A E := incl (⟨ν, hνA⟩ : A) a with hudef
  set f : Pt d → ModelSpace A E := fun y => Gam y x u - u with hfdef
  -- components of `u` in degrees `< ν` vanish
  have hproju : ∀ b : A, (b : ℝ) < ν → proj b u = 0 := by
    intro b hb
    have hne : b ≠ (⟨ν, hνA⟩ : A) := by
      intro h
      rw [h] at hb
      exact absurd hb (lt_irrefl ν)
    show (DirectSum.of E (⟨ν, hνA⟩ : A) a) b = 0
    exact DirectSum.of_eq_of_ne _ _ _ hne
  -- `f y - Γ_{yz} f z = Γ_{yz} u - u`
  have hdiff : ∀ y z : Pt d, f y - Gam y z (f z) = Gam y z u - u := by
    intro y z
    have h1 : Gam y z (f z) = Gam y x u - Gam y z u := by
      simp only [hfdef, map_sub, hmod.gam_comp y z x u]
    rw [h1]
    simp only [hfdef]
    abel
  -- `f` is a modelled distribution of order `ν`
  have hfmod : IsModelled s ν Gam f := by
    constructor
    · intro y b hb
      have := hT.triangular (Gam y x) (hmod.gam_mem y x) (⟨ν, hνA⟩ : A) b a (by exact_mod_cast hb)
      simpa [hfdef, hudef] using this
    · intro K hK
      obtain ⟨α₀, hα₀⟩ := hT.bddBelow
      obtain ⟨Cg, hCg⟩ := hmod.gam_bound (ν + 1) (by linarith) (insert x K) (hK.insert x)
      -- a uniform bound for the scaled distance to `x` on `K ∪ {x}`
      obtain ⟨ρ, hρ⟩ := (hK.insert x).isBounded.subset_closedBall x
      set B : ℝ := max 1 ρ with hBdef
      have hB1 : (1 : ℝ) ≤ B := le_max_left _ _
      have hsn : ∀ y ∈ insert x K, snorm s (y - x) ≤ B := by
        intro y hy
        apply Real.iSup_le _ (le_trans zero_le_one hB1)
        intro i
        have hyx : ‖y - x‖ ≤ ρ := by
          have := hρ hy
          simpa [Metric.mem_closedBall, dist_eq_norm] using this
        have hcoord : |(y - x) i| ≤ ρ := le_trans (by simpa using norm_le_pi_norm (y - x) i) hyx
        have hp0 : (0 : ℝ) < 1 / (s i : ℝ) := by
          have : (1 : ℝ) ≤ (s i : ℝ) := by exact_mod_cast hs i
          positivity
        have hp1 : (1 : ℝ) / (s i : ℝ) ≤ 1 := by
          have : (1 : ℝ) ≤ (s i : ℝ) := by exact_mod_cast hs i
          rw [div_le_one (by linarith)]
          exact this
        rcases le_or_gt |(y - x) i| 1 with hle | hgt
        · exact le_trans (Real.rpow_le_one (abs_nonneg _) hle hp0.le) hB1
        · calc |(y - x) i| ^ ((1 : ℝ) / (s i : ℝ))
              ≤ |(y - x) i| ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hgt.le hp1
            _ = |(y - x) i| := Real.rpow_one _
            _ ≤ B := le_trans hcoord (le_max_right _ _)
      set Cg' : ℝ := max Cg 0 with hCg'def
      have hCg'0 : (0 : ℝ) ≤ Cg' := le_max_right _ _
      have hCgle : Cg ≤ Cg' := le_max_left _ _
      have hBpow : (1 : ℝ) ≤ B ^ (ν - α₀) := Real.one_le_rpow hB1 (by
        have : α₀ ≤ ν := hα₀ hνA
        linarith)
      refine ⟨Cg' * ‖a‖ * B ^ (ν - α₀), ?_, ?_⟩
      · -- pointwise bound
        intro y hy b hb
        have hmemy : y ∈ insert x K := Set.mem_insert_of_mem x hy
        have hmemx : x ∈ insert x K := Set.mem_insert x K
        have hbnu : (b : ℝ) < ((⟨ν, hνA⟩ : A) : ℝ) := hb
        have hgam := hCg (⟨ν, hνA⟩ : A) b (by show ν < ν + 1; linarith) hbnu a y hmemy x hmemx
        have hpf : proj b (f y) = proj b (Gam y x u) := by
          simp only [hfdef, map_sub, hproju b hb, sub_zero]
        rw [hpf]
        have hstep1 : ‖proj b (Gam y x u)‖ ≤ Cg' * ‖a‖ * snorm s (y - x) ^ (ν - (b : ℝ)) := by
          refine le_trans hgam ?_
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by
            apply Real.iSup_nonneg
            intro i
            positivity) _)
          exact mul_le_mul_of_nonneg_right hCgle (norm_nonneg _)
        refine le_trans hstep1 ?_
        have hsnn : 0 ≤ snorm s (y - x) := by
          apply Real.iSup_nonneg
          intro i
          positivity
        have hexp : ν - (b : ℝ) ≤ ν - α₀ := by
          have : α₀ ≤ (b : ℝ) := hα₀ b.2
          linarith
        have hpow : snorm s (y - x) ^ (ν - (b : ℝ)) ≤ B ^ (ν - α₀) := by
          calc snorm s (y - x) ^ (ν - (b : ℝ))
              ≤ B ^ (ν - (b : ℝ)) := by
                apply Real.rpow_le_rpow hsnn (hsn y hmemy)
                linarith
            _ ≤ B ^ (ν - α₀) := Real.rpow_le_rpow_of_exponent_le hB1 hexp
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
      · -- Hölder bound
        intro y hy z hz _ b hb
        have hmemy : y ∈ insert x K := Set.mem_insert_of_mem x hy
        have hmemz : z ∈ insert x K := Set.mem_insert_of_mem x hz
        have hbnu : (b : ℝ) < ((⟨ν, hνA⟩ : A) : ℝ) := hb
        have hgam := hCg (⟨ν, hνA⟩ : A) b (by show ν < ν + 1; linarith) hbnu a y hmemy z hmemz
        have hpf : proj b (f y - Gam y z (f z)) = proj b (Gam y z u) := by
          rw [hdiff y z]
          simp only [map_sub, hproju b hb, sub_zero]
        rw [hpf]
        have hsnn : (0:ℝ) ≤ snorm s (y - z) ^ (ν - (b : ℝ)) := by
          apply Real.rpow_nonneg
          apply Real.iSup_nonneg
          intro i
          positivity
        have h1 : ‖proj b (Gam y z u)‖ ≤ Cg' * ‖a‖ * snorm s (y - z) ^ (ν - (b : ℝ)) := by
          refine le_trans hgam ?_
          apply mul_le_mul_of_nonneg_right _ hsnn
          exact mul_le_mul_of_nonneg_right hCgle (norm_nonneg _)
        refine le_trans h1 ?_
        apply mul_le_mul_of_nonneg_right _ hsnn
        calc Cg' * ‖a‖ = Cg' * ‖a‖ * 1 := (mul_one _).symm
          _ ≤ Cg' * ‖a‖ * B ^ (ν - α₀) :=
              mul_le_mul_of_nonneg_left hBpow (by positivity)
  -- the two models give the same jets, since `f` takes values in degrees `< ν`
  have hagree : ∀ y : Pt d, Pi y (f y) = Pi' y (f y) := by
    intro y
    have hdec : ∑ b ∈ (f y).support, (DirectSum.of E b) ((f y) b) = f y :=
      DirectSum.sum_support_of (f y)
    have hlt : ∀ b ∈ (f y).support, (b : ℝ) < ν := by
      intro b hb
      by_contra hcon
      push Not at hcon
      have : proj b (f y) = 0 := hfmod.vanishing y b hcon
      exact (DFinsupp.mem_support_iff.mp hb) this
    calc Pi y (f y) = Pi y (∑ b ∈ (f y).support, (DirectSum.of E b) ((f y) b)) := by rw [hdec]
      _ = ∑ b ∈ (f y).support, Pi y ((DirectSum.of E b) ((f y) b)) := by rw [map_sum]
      _ = ∑ b ∈ (f y).support, Pi' y ((DirectSum.of E b) ((f y) b)) := by
            refine Finset.sum_congr rfl fun b hb => ?_
            exact hlow b (hlt b hb) ((f y) b) y
      _ = Pi' y (∑ b ∈ (f y).support, (DirectSum.of E b) ((f y) b)) := by rw [map_sum]
      _ = Pi' y (f y) := by rw [hdec]
  -- the identity `Π_x u - Π_y f(y) = Π_y u`
  have hkey : ∀ (P : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d), IsModel s r G P Gam →
      ∀ y : Pt d, P x u - P y (f y) = P y u := by
    intro P hP y
    have h1 : P y (Gam y x u) = P x u := by
      rw [hP.pi_comp x y (Gam y x u), hP.gam_comp x y x u, hP.gam_self x u]
    have h2 : P y (f y) = P x u - P y u := by
      simp only [hfdef, map_sub, h1]
    rw [h2]
    abel
  -- both candidates satisfy the reconstruction bound for `f`
  have hbound : ∀ (P : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d), IsModel s r G P Gam →
      ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ y ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∀ η : Pt d → ℝ, IsTestBall s r η →
          |(P x u - P y (f y)).eval (scaledTest s δ y η)| ≤ C * δ ^ ν := by
    intro P hP K hK
    obtain ⟨Cp, hCp⟩ := hP.pi_bound (ν + 1) (by linarith) K hK
    refine ⟨max Cp 0 * ‖a‖, ?_⟩
    intro y hy δ hδ0 hδ1 η hη
    rw [hkey P hP y]
    have hb := hCp (⟨ν, hνA⟩ : A) (by show ν < ν + 1; linarith) a y hy δ hδ0 hδ1 η hη
    refine le_trans hb ?_
    have hδν : (0:ℝ) ≤ δ ^ ν := Real.rpow_nonneg hδ0.le _
    apply mul_le_mul_of_nonneg_right _ hδν
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hξ : ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ y ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ η : Pt d → ℝ, IsTestBall s r η →
        |(Pi x u - Pi y (f y)).eval (scaledTest s δ y η)| ≤ C * δ ^ ν :=
    fun K hK => hbound Pi hmod K hK
  have hζ : ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ y ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ η : Pt d → ℝ, IsTestBall s r η →
        |(Pi' x u - Pi y (f y)).eval (scaledTest s δ y η)| ≤ C * δ ^ ν := by
    intro K hK
    obtain ⟨C, hC⟩ := hbound Pi' hmod' K hK
    refine ⟨C, ?_⟩
    intro y hy δ hδ0 hδ1 η hη
    rw [hagree y]
    exact hC y hy δ hδ0 hδ1 η hη
  show Pi x u = Pi' x u
  exact Hairer.reconstruction_uniqueness hs hT hmod hν hfmod (Pi x u) (Pi' x u) hξ hζ
