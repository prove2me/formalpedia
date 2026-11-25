-- Prove2me | solution 1 for GlobalTheory.ArtinKernel.exists_linear_of_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:47:57.804284+00:00
-- url     : https://prove2.me/submissions/51b5bfd1-f880-4779-8ec4-ba831ab3353a

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnFamPtAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfLogDeriv
import Theorems.Thm_GlobalTheory_ArtinKernel_ex_add_lattice
import Theorems.Thm_GlobalTheory_ArtinKernel_exists_chart
import Theorems.Thm_GlobalTheory_ArtinKernel_evalPt_gen_two
import Theorems.Thm_GlobalTheory_ArtinKernel_exists_glue
import Theorems.Thm_GlobalTheory_ArtinKernel_exists_linear_of_mul_period
import Theorems.Thm_GlobalTheory_ThetaGroupFrame_top_le_inf
import Theorems.Thm_GlobalTheory_ThetaGroupFrame_top_le_wchart_two


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.ArtinKernel
open GlobalTheory.TangentOrigin
variable {R : Type} [CommRing R] [Algebra ℂ R] [IsLocalRing R] [Module.Finite ℂ R]
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.ArtinKernel
theorem _root_.solution (hL : L.IsLB) (a : u.Λ → ℂ) (B : u.Λ → ((Fin g → ℂ) →ₗ[ℂ] ℂ)) (ha : ∀ l, a l ≠ 0)
    (hfr : ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = a l * cexp (B l z) * u.fr i (z + l))
    {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) (x : T ⟶ A) (w : Fin g → ℂ) (hw : p ≫ x = u.ex w)
    (hp : ∀ (V : (T ⊗ A).left.Opens) (f : Γ((T ⊗ A).left, V)),
      DifferentiableOn ℂ (fun z => valAt' (lift p (u.ex z)).left V f) {z | ⊤ ≤ (lift p (u.ex z)).left ⁻¹ᵁ V})
    (c : LB.Gen (Out.translDiff A L x)) (hc : c.IsGen) :
    ∃ lam : (Fin g → ℂ) →ₗ[ℂ] ℂ, ∀ l : u.Λ, cexp (B l w) = cexp (lam l) := by
  classical
  set φ₀ := (lift (fst T A ≫ x) (snd T A) ≫ μ).left with hφ₀
  set φ₁ := (snd T A).left with hφ₁
  have hP0 : ∀ z, (lift p (u.ex z)).left ≫ φ₀ = (u.ex (w + z)).left := by
    intro z
    rw [hφ₀, ← Over.comp_left, ← Category.assoc, comp_lift, lift_fst_assoc, lift_snd, ← Hom.mul_def, hw,
      ← u.ex_add]
  have hP1 : ∀ z, (lift p (u.ex z)).left ≫ φ₁ = (u.ex z).left := by
    intro z
    rw [hφ₁, ← Over.comp_left, lift_snd]
  let O : L.ι → Set (Fin g → ℂ) := fun i => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i}
  have hO : ∀ i, IsOpen (O i) := fun i => (u.hol (L.U i) 0).1
  let D : (Fin 2 → L.ι) → Set (Fin g → ℂ) := fun j =>
    {z | ⊤ ≤ (lift p (u.ex z)).left ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j}
  have hDmem : ∀ j z, z ∈ D j ↔ w + z ∈ O (j 0) ∧ z ∈ O (j 1) := fun j z =>
    GlobalTheory.ThetaGroupFrame.top_le_wchart_two L φ₀ φ₁ j _ _ _ (hP0 z) (hP1 z)
  have hD : ∀ j, IsOpen (D j) := by
    intro j
    have e : D j = (fun z => w + z) ⁻¹' O (j 0) ∩ O (j 1) := by
      ext z
      exact hDmem j z
    rw [e]
    exact ((hO _).preimage (continuous_const.add continuous_id)).inter (hO _)
  have hcov : ∀ z, ∃ j, z ∈ D j := by
    intro z
    obtain ⟨i₀, h₀⟩ := exists_chart u hL (w + z)
    obtain ⟨i₁, h₁⟩ := exists_chart u hL z
    exact ⟨![i₀, i₁], (hDmem _ z).2 ⟨h₀, h₁⟩⟩
  let cv : (Fin 2 → L.ι) → (Fin g → ℂ) → ℂ := fun j z =>
    valAt' (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) (c.s j).val
  let G : (Fin 2 → L.ι) → (Fin g → ℂ) → ℂ := fun j z => cv j z * u.fr (j 1) z / u.fr (j 0) (w + z)
  have hG : ∀ j, DifferentiableOn ℂ (G j) (D j) := by
    intro j
    have h1 : DifferentiableOn ℂ (cv j) (D j) := hp _ _
    have h2 : DifferentiableOn ℂ (u.fr (j 1)) (D j) :=
      (u.fr_hol (j 1)).mono fun z hz => ((hDmem j z).1 hz).2
    have h3 : DifferentiableOn ℂ (fun z => u.fr (j 0) (w + z)) (D j) :=
      (u.fr_hol (j 0)).comp ((differentiableOn_const w).add differentiableOn_id)
        fun z hz => ((hDmem j z).1 hz).1
    have h4 : DifferentiableOn ℂ (fun z => cv j z * u.fr (j 1) z * (u.fr (j 0) (w + z))⁻¹) (D j) :=
      (h1.mul h2).mul (h3.inv fun z hz => u.fr_ne _ _ ((hDmem j z).1 hz).1)
    simpa only [G, div_eq_mul_inv] using h4
  have hc' : ∀ j j' z, z ∈ D j → z ∈ D j' → G j z = G j' z := by
    intro j j' z hz hz'
    have hz0 : ⊤ ≤ (lift p (u.ex z)).left ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j := hz
    have hz1 : ⊤ ≤ (lift p (u.ex z)).left ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j' := hz'
    obtain ⟨a0, a1⟩ := (hDmem j z).1 hz
    obtain ⟨b0, b1⟩ := (hDmem j' z).1 hz'
    have i0 : ⊤ ≤ (u.ex (w + z)).left ⁻¹ᵁ (L.U (j 0) ⊓ L.U (j' 0)) :=
      GlobalTheory.ThetaGroupFrame.top_le_inf _ a0 b0
    have i1 : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U (j 1) ⊓ L.U (j' 1)) := GlobalTheory.ThetaGroupFrame.top_le_inf _ a1 b1
    have e : evalPt (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) hz0 (c.s j).val *
          evalPt (u.ex z).left _ i1 (L.g (j 1) (j' 1)).val =
        evalPt (u.ex (w + z)).left _ i0 (L.g (j 0) (j' 0)).val *
          evalPt (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j') hz1 (c.s j').val :=
      evalPt_gen_two L φ₀ φ₁ c hc (lift p (u.ex z)).left _ _ (hP0 z) (hP1 z) j j' hz0 hz1 i0 i1
    have f0 := u.fr_compat (j 0) (j' 0) (w + z) i0
    have f1 := u.fr_compat (j 1) (j' 1) z i1
    rw [valAt'_eq_evalPt _ _ i0] at f0
    rw [valAt'_eq_evalPt _ _ i1] at f1
    have n0 := u.fr_ne _ _ b0
    have ng : evalPt (u.ex (w + z)).left _ i0 (L.g (j 0) (j' 0)).val ≠ 0 := by
      intro h0
      have h5 := u.fr_ne _ _ a0
      rw [f0, h0, zero_mul] at h5
      exact h5 rfl
    have v0 : valAt' (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) (c.s j).val =
        evalPt (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) hz0 (c.s j).val := valAt'_eq_evalPt _ _ hz0 _
    have v1 : valAt' (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j') (c.s j').val =
        evalPt (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j') hz1 (c.s j').val := valAt'_eq_evalPt _ _ hz1 _
    simp only [G, cv]
    rw [v0, v1, f0, f1, div_eq_div_iff (mul_ne_zero ng n0) n0]
    linear_combination (u.fr (j' 1) z * u.fr (j' 0) (w + z)) * e
  obtain ⟨F, hF, hFG⟩ := exists_glue D G hD hcov hG hc'
  have hne : ∀ z, F z ≠ 0 := by
    intro z
    obtain ⟨j, hz⟩ := hcov z
    have hz0 : ⊤ ≤ (lift p (u.ex z)).left ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j := hz
    obtain ⟨a0, a1⟩ := (hDmem j z).1 hz
    rw [hFG j z hz]
    have v0 : valAt' (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) (c.s j).val =
        evalPt (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) hz0 (c.s j).val := valAt'_eq_evalPt _ _ hz0 _
    simp only [G, cv]
    rw [v0]
    exact div_ne_zero (mul_ne_zero ((c.s j).isUnit.map
      (evalPt (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) hz0)).ne_zero (u.fr_ne _ _ a1)) (u.fr_ne _ _ a0)
  have hper : ∀ (l : u.Λ) z, F (z + l) = cexp (B l w) * F z := by
    intro l z
    obtain ⟨j, hz⟩ := hcov z
    obtain ⟨a0, a1⟩ := (hDmem j z).1 hz
    have hl : (l : Fin g → ℂ) ∈ u.Λ := l.2
    have ez : u.ex (z + l) = u.ex z := ex_add_lattice u z hl
    have ewz : u.ex (w + z + l) = u.ex (w + z) := ex_add_lattice u _ hl
    have hzl : z + l ∈ D j := by
      rw [hDmem]
      refine ⟨?_, ?_⟩
      · show ⊤ ≤ (u.ex (w + (z + l))).left ⁻¹ᵁ _
        rw [← add_assoc, ewz]
        exact a0
      · show ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ _
        rw [ez]
        exact a1
    have n0 : u.fr (j 0) (w + z + l) ≠ 0 := by
      apply u.fr_ne
      show ⊤ ≤ (u.ex (w + z + l)).left ⁻¹ᵁ _
      rw [ewz]
      exact a0
    rw [hFG j _ hzl, hFG j z hz]
    simp only [G, cv]
    rw [ez, ← add_assoc]
    have h1 := hfr l (j 1) z a1
    have h0 := hfr l (j 0) (w + z) a0
    rw [h1, h0, map_add, Complex.exp_add]
    have hal := ha l
    field_simp
  obtain ⟨lam, hlam⟩ := exists_linear_of_mul_period hF hne (S := (u.Λ : Set (Fin g → ℂ))) u.full
    (fun l => cexp (B ⟨l.1, l.2⟩ w)) (fun l z => hper ⟨l.1, l.2⟩ z)
  exact ⟨lam, fun l => hlam ⟨l.1, l.2⟩⟩
end GlobalTheory.ArtinKernel
