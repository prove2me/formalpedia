-- Prove2me | solution 1 for GlobalTheory.PrimUnif.exists_unif_of_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:36:18.252672+00:00
-- url     : https://prove2.me/submissions/06777662-a8b1-47fc-a785-3d775506fe4c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLatticeUniformisationOfPrimTheta
import Theorems.Thm_GlobalTheory_PrimUnif_ex_nsmul
import Theorems.Thm_P2M_GlobalTheory_PrimUnif_unitOn_inj__d34e40355634
import Theorems.Thm_GlobalTheory_PrimUnif_unitS_spMap
import Theorems.Thm_GlobalTheory_SelfCube_appellHumbert_data_of_iso_cube
import Theorems.Thm_GlobalTheory_holFamily_lift
import Theorems.Thm_P2M_GlobalTheory_valAt__rules_bb0546efa0f1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.PrimUnif
namespace GlobalTheory.PrimUnif
theorem _root_.solution :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t : TObj g k J b (spMap em)), t.Prim w w' → ∃ (La : Type) (_ : AddCommGroup La) (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), Function.Bijective EF ∧ (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) ∧ (∀ i₁ i₂, Complex.exp (-(2 * Real.pi * Complex.I) * (EF (lam i₁) (lam i₂) : ℂ) / ((k : ℕ) : ℂ)) = em (b.ζ : o) ^ Out.stdSymp g i₁ i₂) ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  intro hL _ _ hU o _ g k J b em w w' t hP
  have hk : ((k : ℕ) : ℂ) ≠ 0 := by
    have h := b.unit.map em
    rw [map_natCast] at h
    exact h.ne_zero
  obtain ⟨rig, hrig⟩ := t.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, hEnd, -, hEf, hEfb, hWeil⟩ := hU t.pol rig hrig
  choose F hF using fun j => hEnd (t.act j) (t.hom j)
  have hone : ∀ j, (1 : 𝟙_ (Over (Sp ℂ)) ⟶ t.A) ≫ t.act j = 1 := fun j => by
    have := t.hom j
    simp [Hom.one_def]
  have hFm : ∀ j (l : u.Λ), F j l ∈ u.Λ := fun j l => by
    rw [← u.ker, hF, (u.ker _).2 l.2]
    exact hone j
  choose z hz using fun i => u.ex_onto (t.pt i)
  have hlam : ∀ i, ((k : ℕ) : ℂ) • z i ∈ u.Λ := fun i => by
    rw [← u.ker, ex_nsmul, hz]
    exact t.torsion i
  have hlev : ∀ i, u.ex (((k : ℕ) : ℂ)⁻¹ • (((k : ℕ) : ℂ) • z i)) = t.pt i := fun i => by
    rw [inv_smul_smul₀ hk, hz]
  refine ⟨u.Λ, inferInstance, Ef, fun i => ⟨_, hlam i⟩, fun j x => ⟨F j x, hFm j x⟩,
    u.Λ.subtype.toAddMonoidHom, Hm, hEfb, ⟨Subtype.val_injective, ?_, ?_, hAH.1, hAH.2.1,
      fun x y => (hEf x y).symm⟩, ?_, u, χ, hAH, ?_, ?_, ?_, ?_⟩
  · have key : ∀ S : AddSubgroup (Fin g → ℂ), (∀ x, x ∈ S ↔ x ∈ u.Λ) → DiscreteTopology S := by
      intro S hS
      obtain rfl : S = u.Λ.toAddSubgroup := AddSubgroup.ext hS
      exact u.discrete
    refine key _ (fun x => ⟨fun h => ?_, fun h => AddMonoidHom.mem_range.2 ⟨⟨x, h⟩, rfl⟩⟩)
    obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.1 h
    exact y.2
  · have hs : Set.range (fun x : u.Λ => (x : Fin t.pol.g → ℂ)) = (u.Λ : Set (Fin t.pol.g → ℂ)) :=
      Subtype.range_coe
    have hfull := u.full
    rw [← hs] at hfull
    exact hfull
  · intro i₁ i₂
    have hkpos : 0 < k := Nat.pos_of_ne_zero (fun h => hk (by simp [h]))
    have hW := hWeil k ⟨_, hlam i₁⟩ ⟨_, hlam i₂⟩
      (Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (Ef ⟨_, hlam i₁⟩ ⟨_, hlam i₂⟩ : ℂ) / ((k : ℕ) : ℂ))))
      hkpos rfl
    simp only [hlev] at hW
    have hP2 := t.pairing i₁ i₂
    rw [unitS_spMap] at hP2
    have hu := ((hL.weil (Sp ℂ) t.pol k (𝟙_ _)).1 (t.pt i₁) (t.pt i₂) (t.torsion i₁) (t.torsion i₂)).unique hW hP2
    have hpow : ∀ (x : ℂˣ) (n : ℤ), unitOn x ^ n = unitOn (x ^ n) := by
      intro x n
      unfold unitOn
      rw [map_zpow]
    rw [hpow] at hu
    have hc := congrArg Units.val (unitOn_inj' hu)
    simpa [Units.val_zpow_eq_zpow_val] using hc
  · intro x
    refine ⟨fun h => AddMonoidHom.mem_range.2 ⟨⟨x, h⟩, rfl⟩, fun h => ?_⟩
    obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.1 h
    exact y.2
  · intro x l hl
    have hv : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) := fun X x => valAt'_rules X x
    have : IsCommMonObj t.pol.A := t.ab.comm
    have hAHd := GlobalTheory.SelfCube.appellHumbert_data_of_iso_cube hv (GlobalTheory.holFamily_lift hv) t.pol u Hm χ Ef
      ⟨hAH.1, hAH.2.2.1, fun a c => hEf a c, hAH.2.2.2⟩ (t.act w) (F w) (fun m hm => hFm w ⟨m, hm⟩) (hF w) hP.2.2
    obtain rfl : l = x := Subtype.ext hl
    exact hAHd.2 l
  · intro i
    exact congrArg (fun p => p.left) (hlev i).symm
  · intro j
    exact ⟨F j, fun x => rfl, hF j⟩
end GlobalTheory.PrimUnif
