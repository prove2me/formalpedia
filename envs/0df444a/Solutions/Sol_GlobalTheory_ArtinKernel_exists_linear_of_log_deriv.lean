-- Prove2me | solution 1 for GlobalTheory.ArtinKernel.exists_linear_of_log_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:47:08.630549+00:00
-- url     : https://prove2.me/submissions/be1ab8f5-2ff1-4571-81a2-11f6e7e9c456

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
import Theorems.Thm_GlobalTheory_ArtinKernel_exists_glue
import Theorems.Thm_GlobalTheory_ArtinKernel_exists_linear_of_add_period
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_fderiv_apply
import Theorems.Thm_GlobalTheory_ThetaGroupFrame_top_le_inf


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
theorem _root_.solution (hL : L.IsLB) (a : u.Λ → ℂ) (B : u.Λ → ((Fin g → ℂ) →ₗ[ℂ] ℂ))
    (ha : ∀ l, a l ≠ 0)
    (hfr : ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = a l * cexp (B l z) * u.fr i (z + l))
    (w : Fin g → ℂ) (K : L.ι → (Fin g → ℂ) → ℂ)
    (hK : ∀ i, DifferentiableOn ℂ (K i) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i})
    (hper : ∀ i z, ∀ l ∈ u.Λ, K i (z + l) = K i z)
    (hKc : ∀ i i' z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i' →
      valAt' (u.ex z).left _ (L.g i i').val * K i z =
        fderiv ℂ (fun y => valAt' (u.ex y).left (L.U i ⊓ L.U i') (L.g i i').val) z w +
          valAt' (u.ex z).left _ (L.g i i').val * K i' z) :
    ∃ lam : (Fin g → ℂ) →ₗ[ℂ] ℂ, ∀ l : u.Λ, B l w = lam l := by
  classical
  let O : L.ι → Set (Fin g → ℂ) := fun i => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i}
  have hO : ∀ i, IsOpen (O i) := fun i => (u.hol (L.U i) 0).1
  let d : L.ι → (Fin g → ℂ) → ℂ := fun i z => fderiv ℂ (u.fr i) z w
  have hd : ∀ i, DifferentiableOn ℂ (d i) (O i) := fun i =>
    GlobalTheory.SCV.differentiableOn_fderiv_apply (hO i) (u.fr_hol i) w
  let G : L.ι → (Fin g → ℂ) → ℂ := fun i z => d i z / u.fr i z - K i z
  have hG : ∀ i, DifferentiableOn ℂ (G i) (O i) := by
    intro i
    have h4 : DifferentiableOn ℂ (fun z => d i z * (u.fr i z)⁻¹ - K i z) (O i) :=
      ((hd i).mul ((u.fr_hol i).inv fun z hz => u.fr_ne i z hz)).sub (hK i)
    simpa only [G, div_eq_mul_inv] using h4
  have hcov : ∀ z, ∃ i, z ∈ O i := fun z => exists_chart u hL z
  have hc : ∀ i i' z, z ∈ O i → z ∈ O i' → G i z = G i' z := by
    intro i i' z hz hz'
    let Gv : (Fin g → ℂ) → ℂ := fun y => valAt' (u.ex y).left (L.U i ⊓ L.U i') (L.g i i').val
    have hOii := (u.hol (L.U i ⊓ L.U i') (L.g i i').val).1
    have hzii : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U i ⊓ L.U i') := GlobalTheory.ThetaGroupFrame.top_le_inf _ hz hz'
    have hGvd : DifferentiableAt ℂ Gv z :=
      ((u.hol (L.U i ⊓ L.U i') (L.g i i').val).2).differentiableAt (hOii.mem_nhds hzii)
    have hfrd : DifferentiableAt ℂ (u.fr i') z := (u.fr_hol i').differentiableAt ((hO i').mem_nhds hz')
    have hev : u.fr i =ᶠ[𝓝 z] fun y => Gv y * u.fr i' y := by
      filter_upwards [hOii.mem_nhds hzii] with y hy
      exact u.fr_compat i i' y hy
    have hdi : d i z = Gv z * d i' z + u.fr i' z * fderiv ℂ Gv z w := by
      show fderiv ℂ (u.fr i) z w = _
      rw [hev.fderiv_eq, fderiv_fun_mul hGvd hfrd]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rfl
    have hfri : u.fr i z = Gv z * u.fr i' z := u.fr_compat i i' z hzii
    have n1 : u.fr i' z ≠ 0 := u.fr_ne i' z hz'
    have nG : Gv z ≠ 0 := by
      intro h0
      have h5 := u.fr_ne i z hz
      rw [hfri, h0, zero_mul] at h5
      exact h5 rfl
    have hKc' : Gv z * K i z = fderiv ℂ Gv z w + Gv z * K i' z := hKc i i' z hz hz'
    have hKi : K i z = fderiv ℂ Gv z w / Gv z + K i' z := by
      field_simp
      linear_combination hKc'
    simp only [G]
    rw [hdi, hfri, hKi]
    field_simp
    ring
  obtain ⟨F, hF, hFG⟩ := exists_glue O G hO hcov hG hc
  have hper' : ∀ (l : u.Λ) z, F (z + l) = F z + -(B l w) := by
    intro l z
    obtain ⟨i, hz⟩ := hcov z
    have hl : (l : Fin g → ℂ) ∈ u.Λ := l.2
    have hzl : z + l ∈ O i := by
      show ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ _
      rw [ex_add_lattice u z hl]
      exact hz
    have hdl : DifferentiableAt ℂ (u.fr i) (z + l) := (u.fr_hol i).differentiableAt ((hO i).mem_nhds hzl)
    have h1 : HasFDerivAt (fun y => a l * cexp (B l y)) ((a l * cexp (B l z)) • (B l).toContinuousLinearMap) z := by
      have h7 := ((Complex.hasDerivAt_exp (B l z)).comp_hasFDerivAt z
        (B l).toContinuousLinearMap.hasFDerivAt).const_mul (a l)
      simpa [smul_smul] using h7
    have h2 : HasFDerivAt (fun y => u.fr i (y + l)) (fderiv ℂ (u.fr i) (z + l)) z :=
      (hasFDerivAt_comp_add_right (l : Fin g → ℂ)).2 hdl.hasFDerivAt
    have h3 : HasFDerivAt (fun y => a l * cexp (B l y) * u.fr i (y + l))
        ((a l * cexp (B l z)) • fderiv ℂ (u.fr i) (z + l) +
          u.fr i (z + l) • ((a l * cexp (B l z)) • (B l).toContinuousLinearMap)) z := h1.mul h2
    have hev : u.fr i =ᶠ[𝓝 z] fun y => a l * cexp (B l y) * u.fr i (y + l) := by
      filter_upwards [(hO i).mem_nhds hz] with y hy
      exact hfr l i y hy
    have hdz : d i z = a l * cexp (B l z) * d i (z + l) + u.fr i (z + l) * (a l * cexp (B l z) * B l w) := by
      show fderiv ℂ (u.fr i) z w = _
      rw [hev.fderiv_eq, h3.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        LinearMap.coe_toContinuousLinearMap']
      rfl
    have n1 : u.fr i (z + l) ≠ 0 := u.fr_ne i _ hzl
    have hal := ha l
    rw [hFG i _ hzl, hFG i z hz]
    simp only [G]
    rw [hdz, hfr l i z hz, ← hper i z l hl]
    field_simp
    ring
  obtain ⟨lam, hlam⟩ := exists_linear_of_add_period hF (S := (u.Λ : Set (Fin g → ℂ))) u.full
    (fun l => -(B ⟨l.1, l.2⟩ w)) (fun l z => hper' ⟨l.1, l.2⟩ z)
  refine ⟨-lam, fun l => ?_⟩
  have h6 : -(B l w) = lam l := hlam ⟨l.1, l.2⟩
  rw [LinearMap.neg_apply, ← h6, neg_neg]
end GlobalTheory.ArtinKernel
