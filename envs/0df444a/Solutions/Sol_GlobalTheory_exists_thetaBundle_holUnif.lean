-- Prove2me | solution 1 for GlobalTheory.exists_thetaBundle_holUnif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:16.119091+00:00
-- url     : https://prove2.me/submissions/b341e3f0-0703-450c-9e5c-fc5713301118

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsMemThetaLevelCharApplyNeZero
import Theorems.Thm_GlobalTheory_exists_isLB_of_frames
import Theorems.Thm_GlobalTheory_autFactor_pow_of_even
import Theorems.Thm_GlobalTheory_thetaLevelChar_eq_thetaLevel_of_even
import Theorems.Thm_GlobalTheory_exists_mem_thetaLevelChar_apply_ne_zero
import Theorems.Thm_GlobalTheory_ComplexPoints_iSup_eq_top_of_complexPoints
import Theorems.Thm_GlobalTheory_ComplexPoints_opens_le_of_complexPoints
import Theorems.Thm_GlobalTheory_IsSiegel_mk
import Theorems.Thm_GlobalTheory_mem_thetaLevelChar_iff_autFactor
import Theorems.Thm_GlobalTheory_mul_mem_thetaLevelChar
import Theorems.Thm_GlobalTheory_pow_mem_thetaLevelChar
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_ex_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply


section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
namespace GlobalTheory
private lemma preimage_whole_of_le {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {V W : Y.Opens} (hVW : V ≤ W)
    (h : ⊤ ≤ x ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ W :=
  fun _ ha => hVW (h ha)
private lemma valAt'_presheaf_map' {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {V W : Y.Opens} (hVW : V ≤ W)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, W)) :
    valAt' x V ((Y.presheaf.map (homOfLE hVW).op).hom f) = valAt' x W f := by
  have hW : ⊤ ≤ x ⁻¹ᵁ W := preimage_whole_of_le x hVW h
  have key : Y.presheaf.map (homOfLE hVW).op ≫ x.appLE V ⊤ h = x.appLE W ⊤ hW := by
    rw [Scheme.Hom.map_appLE]
  simp only [valAt', dif_pos h, dif_pos hW, valAt]
  rw [← key]
  rfl
variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℝ}
end GlobalTheory
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℝ}
namespace GlobalTheory
theorem _root_.solution :
    (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → SiegelSubDomainStatement → ThetaHoloStatement → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → (Differentiable ℂ (fun z => theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta 0 0 z τ) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta 0 0 z τ) z) ∧ (fun z => theta 0 0 z τ) ≠ 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → DiscreteTopology (periodLattice τ) ∧ Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤ ∧ ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X : Over (Sp ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧ (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g → ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠ 0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → Even N → ∀ [GrpObj X], (∀ z w, ex (z + w) = ex z * ex w) → ∀ a b : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) → ∃ (L : LB X.left) (u : HolUnif X L g), L.IsLB ∧ u.ex = ex ∧ (∀ z, z ∈ u.Λ ↔ z ∈ periodLattice τ) ∧ (∀ (n n' : Fin g → ℤ) i z, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U i → u.fr i z = autFactor a b τ n n' z * u.fr i (z + τ *ᵥ ofIntVec n + ofIntVec n')) ∧ (∀ i, ∃ h F : (Fin g → ℂ) → ℂ, (Differentiable ℂ h ∧ ∀ (n n' : Fin g → ℤ) z, h (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * h z) ∧ Differentiable ℂ F ∧ (∀ (n n' : Fin g → ℤ) z, F (z + τ *ᵥ ofIntVec n + ofIntVec n') = autFactor a b τ n n' z * eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * F z) ∧ ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ L.U i ↔ h z ≠ 0 ∧ F z ≠ 0) ∧ u.fr i z = h z / F z)) := by
  intro H1 _ _ _ H5 g τ hτ N hN3 X ex D hX hquot hNe _ hexadd a b ha hb
  obtain ⟨hInt, hProp, hsurj, hker, hhol, -, -⟩ := hX
  have : IsIntegral X.left := hInt
  have : IsProper X.hom := hProp
  have hN0 : N ≠ 0 := by omega
  have hext := H1 X inferInstance inferInstance
  have hlev : ∀ M, Even M → thetaLevelChar a b M τ = thetaLevel M τ :=
    fun M hM => thetaLevelChar_eq_thetaLevel_of_even ha hb hM
  have quot : ∀ p q : (Fin g → ℂ) → ℂ, p ∈ thetaLevelChar a b (N * (N + 2)) τ →
      q ∈ thetaLevelChar a b (N * (N + 2)) τ → ∃ (V : X.left.Opens) (φ : Γ(X.left, V)), ∀ z,
        (⊤ ≤ (ex z).left ⁻¹ᵁ V ↔ q z ≠ 0) ∧ (q z ≠ 0 → valAt' (ex z).left V φ = p z / q z) := by
    intro p q hp hq
    rw [hlev _ (hNe.mul_right _)] at hp hq
    exact hquot (N + 2) p q (mem_thetaLevel.mp hp) (mem_thetaLevel.mp hq)
  let κ : Type := {p : ((Fin g → ℂ) → ℂ) × ((Fin g → ℂ) → ℂ) //
    p.1 ∈ thetaLevel N τ ∧ p.2 ∈ thetaLevelChar a b (N + 1) τ}
  have hF : ∀ i : κ, i.1.2 ∈ thetaLevelChar a b (N + 1) τ := fun i => i.2.2
  have hh : ∀ i : κ, i.1.1 ∈ thetaLevelChar a b N τ := fun i => by
    rw [hlev N hNe]
    exact i.2.1
  have hchart : ∀ i : κ, ∃ V : X.left.Opens, ∀ z,
      (⊤ ≤ (ex z).left ⁻¹ᵁ V ↔ i.1.1 z ≠ 0 ∧ i.1.2 z ≠ 0) := by
    intro i
    have hq : i.1.1 * i.1.2 ^ N ∈ thetaLevelChar a b (N * (N + 2)) τ := by
      have e : N * (N + 2) = N + N * (N + 1) := by ring
      rw [e]
      exact mul_mem_thetaLevelChar (hh i) (pow_mem_thetaLevelChar (hF i) N)
    obtain ⟨V, _, hV⟩ := quot _ _ hq hq
    refine ⟨V, fun z => (hV z).1.trans ?_⟩
    simp only [Pi.mul_apply, Pi.pow_apply, ne_eq, mul_eq_zero, pow_eq_zero_iff hN0, not_or]
  choose V hV using hchart
  let fr : κ → (Fin g → ℂ) → ℂ := fun i z => i.1.1 z / i.1.2 z
  have hfr : ∀ i z, ⊤ ≤ (ex z).left ⁻¹ᵁ V i → fr i z ≠ 0 :=
    fun i z hz => div_ne_zero ((hV i z).1 hz).1 ((hV i z).1 hz).2
  have pt : ∀ x : Sp ℂ ⟶ X.left, x ≫ X.hom = 𝟙 _ → ∃ z, (ex z).left = x := by
    intro x hx
    obtain ⟨z, hz⟩ := hsurj (Over.homMk x (by simpa using hx))
    exact ⟨z, by rw [hz]; rfl⟩
  have hcov : ⨆ i, V i = ⊤ := by
    refine ComplexPoints.iSup_eq_top_of_complexPoints X.hom V fun x hx => ?_
    obtain ⟨z, rfl⟩ := pt x hx
    obtain ⟨F, hFm, hFz⟩ := exists_mem_thetaLevelChar_apply_ne_zero hτ a b hN0 z
    obtain ⟨h, hhm, hhz⟩ := exists_mem_thetaLevelChar_apply_ne_zero hτ 0 0 (k := N - 1) (by omega) z
    rw [Nat.sub_add_cancel (by omega), thetaLevelChar_zero] at hhm
    exact ⟨⟨(h, F), hhm, hFm⟩, (hV _ z).2 ⟨hhz, hFz⟩⟩
  have hreg : ∀ i j : κ, ∃ φ : Γ(X.left, V i ⊓ V j), ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ (V i ⊓ V j) →
      valAt' (ex z).left (V i ⊓ V j) φ = fr i z / fr j z := by
    intro i j
    have hp : i.1.1 * j.1.2 * i.1.2 ^ (N - 1) ∈ thetaLevelChar a b (N * (N + 2)) τ := by
      have e : N * (N + 2) = N + (N + 1) + (N - 1) * (N + 1) := by
        obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
        rw [hM, Nat.add_sub_cancel]
        ring
      rw [e]
      exact mul_mem_thetaLevelChar (mul_mem_thetaLevelChar (hh i) (hF j)) (pow_mem_thetaLevelChar (hF i) _)
    have hq : j.1.1 * i.1.2 ^ N ∈ thetaLevelChar a b (N * (N + 2)) τ := by
      have e : N * (N + 2) = N + N * (N + 1) := by ring
      rw [e]
      exact mul_mem_thetaLevelChar (hh j) (pow_mem_thetaLevelChar (hF i) N)
    obtain ⟨W, φ, hW⟩ := quot _ _ hp hq
    have hVW : V i ⊓ V j ≤ W := by
      refine ComplexPoints.opens_le_of_complexPoints X.hom _ _ fun x hx hxV => ?_
      obtain ⟨z, rfl⟩ := pt x hx
      have hi := (hV i z).1 (preimage_whole_of_le _ inf_le_left hxV)
      have hj := (hV j z).1 (preimage_whole_of_le _ inf_le_right hxV)
      refine (hW z).1.2 ?_
      simp only [Pi.mul_apply, Pi.pow_apply]
      exact mul_ne_zero hj.1 (pow_ne_zero _ hi.2)
    refine ⟨(X.left.presheaf.map (homOfLE hVW).op).hom φ, fun z hz => ?_⟩
    have hi := (hV i z).1 (preimage_whole_of_le _ inf_le_left hz)
    have hj := (hV j z).1 (preimage_whole_of_le _ inf_le_right hz)
    have hq0 : (j.1.1 * i.1.2 ^ N) z ≠ 0 := by
      simp only [Pi.mul_apply, Pi.pow_apply]
      exact mul_ne_zero hj.1 (pow_ne_zero _ hi.2)
    rw [valAt'_presheaf_map' _ hVW hz, (hW z).2 hq0]
    have hpow : i.1.2 z ^ N = i.1.2 z ^ (N - 1) * i.1.2 z := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    simp only [fr, Pi.mul_apply, Pi.pow_apply]
    rw [hpow]
    have h1 := hi.1
    have h2 := hi.2
    have h3 := hj.1
    have h4 := hj.2
    field_simp
  obtain ⟨tr, hLB, hcompat⟩ := exists_isLB_of_frames X ex hsurj hext V hcov fr hfr hreg
  have hex0 : ex 0 = 1 := by
    obtain ⟨z1, hz1⟩ := hsurj 1
    have := hexadd z1 0
    rw [add_zero, hz1, _root_.one_mul] at this
    exact this.symm
  let u : HolUnif X (LB.mk κ V tr) g :=
    { ex := ex
      ex_add := hexadd
      ex_onto := hsurj
      Λ := (periodLattice τ).toIntSubmodule
      ker := fun z => by
        rw [← hex0, hker, sub_zero]
        exact Iff.rfl
      discrete := (H5 g τ hτ).1
      full := (H5 g τ hτ).2.1
      hol := fun W f => by
        simpa only [Set.mem_univ, true_and] using hhol W f
      fr := fr
      fr_hol := fun i => by
        have dh := (mem_thetaLevel.mp i.2.1).1
        have dF := (mem_thetaLevelChar.mp i.2.2).1
        intro z hz
        have hd := (dh z).mul ((dF z).inv ((hV i z).1 hz).2)
        exact (hd.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun w => div_eq_mul_inv _ _)).differentiableWithinAt
      fr_ne := hfr
      fr_compat := hcompat }
  refine ⟨LB.mk κ V tr, u, hLB, rfl, fun z => Iff.rfl, ?_, ?_⟩
  · intro n n' i z hz
    have hi := (hV i z).1 hz
    have hA : autFactor a b τ n n' z ≠ 0 := by
      rw [autFactor]
      exact mul_ne_zero (eC_ne_zero _) (eC_ne_zero _)
    have h1 := (mem_thetaLevelChar_iff_autFactor.mp (hh i)).2 n n' z
    have h2 := (mem_thetaLevelChar_iff_autFactor.mp (hF i)).2 n n' z
    show i.1.1 z / i.1.2 z = autFactor a b τ n n' z *
      (i.1.1 (z + τ *ᵥ ofIntVec n + ofIntVec n') / i.1.2 (z + τ *ᵥ ofIntVec n + ofIntVec n'))
    rw [h1, h2, pow_succ]
    have h3 := hi.2
    have h4 := pow_ne_zero N hA
    field_simp
  · intro i
    refine ⟨i.1.1, i.1.2, mem_thetaLevel.mp i.2.1, (mem_thetaLevelChar.mp i.2.2).1,
      fun n n' z => ?_, fun z => ⟨hV i z, rfl⟩⟩
    rw [(mem_thetaLevelChar_iff_autFactor.mp i.2.2).2 n n' z, pow_succ', autFactor_pow_of_even ha hb hNe]
end GlobalTheory
