-- Prove2me | solution 1 for GlobalTheory.ThetaFn.exists_hasAnConst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:48:24.578683+00:00
-- url     : https://prove2.me/submissions/de76f699-ed9c-4194-874e-746f8419a285

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff
import Theorems.Thm_GlobalTheory_ThetaFn_exists_entire_twist
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_translPt
import Theorems.Thm_GlobalTheory_ThetaFn_exists_int_of_exp_eq_one
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_add_left
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_swap
import Theorems.Thm_GlobalTheory_appellHumbert_trivial_of_nowhere_vanishing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
namespace GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter AppellHumbertTrivial
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
private theorem exists_algChart_mem_source (hL : L.IsLB) (f : Sp ℂ ⟶ A.left) : ∃ i, ⊤ ≤ f ⁻¹ᵁ L.U i := by
  obtain ⟨cover, -, -⟩ := hL
  obtain ⟨a0⟩ : Nonempty (PrimeSpectrum ℂ) := inferInstance
  have hmem : f.base a0 ∈ (⨆ i, L.U i) := by
    rw [cover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  refine ⟨i, fun a _ => ?_⟩
  have hsub : a = a0 := Subsingleton.elim (α := PrimeSpectrum ℂ) a a0
  rw [hsub]
  exact hi
variable {u p} {Hm : Matrix (Fin g) (Fin g) ℂ} {k : ℤ} {Θ : ThetaGrp A L k T} {x : Fin g → ℂ}
private theorem mul_zpow_eq_of_two_zpow_relations {V r r' q a0 f0 f1 W : ℂ} (k : ℤ) (hq : q ≠ 0) (ha : a0 ≠ 0)
    (hf : f0 ≠ 0) (e1 : V * (q * (a0 * W) * f1) ^ k = r * (q * a0 * f0) ^ k)
    (e2 : V * f1 ^ k = r' * f0 ^ k) : r' * W ^ k = r := by
  simp only [mul_zpow] at e1
  have hne : q ^ k * a0 ^ k * f0 ^ k ≠ 0 :=
    mul_ne_zero (mul_ne_zero (zpow_ne_zero _ hq) (zpow_ne_zero _ ha)) (zpow_ne_zero _ hf)
  apply mul_right_cancel₀ hne
  linear_combination e1 - (q ^ k * a0 ^ k * W ^ k) * e2
private theorem complex_star_eq_sub_two_I_mul_im (w : ℂ) : star w = w - 2 * Complex.I * (w.im : ℂ) := by
  apply Complex.ext <;> simp <;> ring
end GlobalTheory.ThetaFn
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter AppellHumbertTrivial
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {u p} {Hm : Matrix (Fin g) (Fin g) ℂ} {k : ℤ} {Θ : ThetaGrp A L k T} {x : Fin g → ℂ}
namespace GlobalTheory.ThetaFn
theorem _root_.solution (hL : L.IsLB) {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ)
    (hx : p ≫ Θ.pt = u.ex x) :
    (∀ l ∈ u.Λ, ∃ n : ℤ, k * (hermForm Hm x l).im = n) ∧ ∃ c, HasAnConst u p Hm Θ x c := by
  obtain ⟨r, hrd, hr0, hr⟩ := exists_entire_twist u p hL (m := translPt A Θ.pt) (a := k) (b := k)
    Θ.φ Θ.isGen (w := fun z => z + x) (differentiable_id.add_const x) (fun z => exAt_translPt u hx z)
  have hr' : ∀ (j : Fin 2 → L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) →
      ⊤ ≤ (u.ex (z + x)).left ⁻¹ᵁ L.U (j 1) →
      valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, (translPt A Θ.pt).left] j) (Θ.φ.s j).val *
        u.fr (j 1) (z + x) ^ k = r z * u.fr (j 0) z ^ k :=
    fun j z h0 h1 => hr j z h0 h1
  have hper : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := by
    intro l z
    rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
  have R1 : ∀ (l : u.Λ) z,
      r (z + l) * Complex.exp (Real.pi * (x ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) ^ k = r z := by
    intro l z
    obtain ⟨i0, hi0⟩ := exists_algChart_mem_source hL (u.ex z).left
    obtain ⟨i1, hi1⟩ := exists_algChart_mem_source hL (u.ex (z + x)).left
    have hi0' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i0 := by
      rw [hper]
      exact hi0
    have hi1' : ⊤ ≤ (u.ex (z + l + x)).left ⁻¹ᵁ L.U i1 := by
      rw [add_right_comm, hper]
      exact hi1
    have hexAt : exAt u p (z + l) = exAt u p z := by
      unfold exAt
      rw [hper]
    have e1 : valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, (translPt A Θ.pt).left] ![i0, i1])
        (Θ.φ.s ![i0, i1]).val * u.fr i1 (z + x) ^ k = r z * u.fr i0 z ^ k := hr' ![i0, i1] z hi0 hi1
    have e2 : valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, (translPt A Θ.pt).left] ![i0, i1])
        (Θ.φ.s ![i0, i1]).val * u.fr i1 (z + x + l) ^ k = r (z + l) * u.fr i0 (z + l) ^ k := by
      have h2 := hr' ![i0, i1] (z + l) hi0' hi1'
      rw [hexAt, add_right_comm] at h2
      exact h2
    have a0 := hAH.2.2.2 l i0 z hi0
    have a1 := hAH.2.2.2 l i1 (z + x) hi1
    have hE : Complex.exp (Real.pi * ((z + x) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) =
        Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
          Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) *
        Complex.exp (Real.pi * (x ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) := by
      rw [add_dotProduct, ← Complex.exp_add]
      congr 1
      ring
    rw [a0, a1, hE] at e1
    have hχ : χ l ≠ 0 := by
      intro h0
      have := hAH.2.2.1 l
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    exact mul_zpow_eq_of_two_zpow_relations k hχ (Complex.exp_ne_zero _) (u.fr_ne _ _ hi0') e1 e2
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (Fin g → ℂ) → ℂ, ∀ z, ρ z = r z *
      Complex.exp (k * Real.pi * hermForm Hm z x + k * Real.pi * hermForm Hm x x / 2) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨cf, hcf⟩ : ∃ cf : u.Λ → ℂ, ∀ l, cf l =
      Complex.exp (-(2 * Real.pi * Complex.I * (((k : ℝ) * (hermForm Hm x l).im : ℝ) : ℂ))) :=
    ⟨_, fun _ => rfl⟩
  have hB := hAH.1
  have R2 : ∀ (l : u.Λ) z, ρ (z + l) = cf l * ρ z := by
    intro l z
    have hr1 : r (z + l) = r z * Complex.exp (-(k * Real.pi * hermForm Hm x l)) := by
      rw [← R1 l z, ← Complex.exp_int_mul, _root_.mul_assoc, ← Complex.exp_add]
      have h0 : (k : ℂ) * (Real.pi * (x ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) +
          -(k * Real.pi * hermForm Hm x l) = 0 := by
        unfold hermForm
        ring
      rw [h0, Complex.exp_zero, _root_.mul_one]
    rw [hρ, hρ, hr1, hcf, _root_.mul_assoc, ← Complex.exp_add, _root_.mul_left_comm, ← Complex.exp_add]
    congr 2
    rw [hermForm_add_left, hermForm_swap hB x (l : Fin g → ℂ), complex_star_eq_sub_two_I_mul_im]
    push_cast
    ring
  have hρd : Differentiable ℂ ρ := by
    have hfun : ρ = fun z => r z *
        Complex.exp (k * Real.pi * hermForm Hm z x + k * Real.pi * hermForm Hm x x / 2) := funext hρ
    rw [hfun]
    simp only [hermForm, dotProduct]
    fun_prop
  have hρ0 : ∀ z, ρ z ≠ 0 := fun z => by
    rw [hρ]
    exact mul_ne_zero (hr0 z) (Complex.exp_ne_zero _)
  have hcn : ∀ l, ‖cf l‖ = 1 := by
    intro l
    rw [hcf, Complex.norm_exp]
    simp
  have := u.discrete
  obtain ⟨-, hc1, hconst⟩ := appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full 0 cf ρ
    Matrix.isHermitian_zero hcn hρd hρ0 (fun l z => by
      rw [R2 l z]
      simp [hermForm])
  refine ⟨fun l hl => exists_int_of_exp_eq_one (by have h1 := hc1 ⟨l, hl⟩; rw [hcf] at h1; exact h1), ρ 0, hx,
    fun j z h0 h1 => ?_⟩
  rw [hr' j z h0 h1, ← hconst z, hρ]
  have hEF : Complex.exp (k * Real.pi * hermForm Hm z x + k * Real.pi * hermForm Hm x x / 2) *
      fockFactor Hm k x z = 1 := by
    unfold fockFactor
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    ring
  linear_combination (-(r z * u.fr (j 0) z ^ k)) * hEF
end GlobalTheory.ThetaFn
