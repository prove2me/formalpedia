-- Prove2me | solution 1 for GlobalTheory.LocLift.holomorphic_map_lifts_to_periods
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:03:18.243881+00:00
-- url     : https://prove2.me/submissions/3ff16066-4276-46da-af91-12b09c74a670

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolLinearLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TwoMulEqOfIsTypeFn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HolomorphicMapModuliLiftsLocallyToPeriods
import Theorems.Thm_GlobalTheory_LocLift_exists_periods
import Theorems.Thm_GlobalTheory_LocLift_isReduced_complex_tensor
import Theorems.Thm_GlobalTheory_LocLift_lattice_comp
import Theorems.Thm_GlobalTheory_LocLift_exists_mulVec_comp
import Theorems.Thm_GlobalTheory_LocLift_exists_equiv_mulVec
import Theorems.Thm_GlobalTheory_LocLift_natCast_mem_level
import Theorems.Thm_GlobalTheory_LocLift_dim_eq
import Theorems.Thm_GlobalTheory_LocLift_isUnit_natCast_of_over
import Theorems.Thm_GlobalTheory_LocLift_section_pow
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_LocLift_HasForm_of_comp
import Theorems.Thm_GlobalTheory_LocLift_IsExp_comp
import Theorems.Thm_GlobalTheory_LocLift_eq_zero_of_small
import Theorems.Thm_GlobalTheory_LocLift_exists_hol_rep
import Theorems.Thm_GlobalTheory_LocLift_hasForm_of_weil
import Theorems.Thm_GlobalTheory_LocLift_hom_nsmul
import Theorems.Thm_GlobalTheory_LocLift_hom_sub_eq_one
import Theorems.Thm_GlobalTheory_LocLift_isHolTo_comp
import Theorems.Thm_GlobalTheory_LocLift_isHolTo_comp_hom
import Theorems.Thm_GlobalTheory_LocLift_isHolTo_congr
import Theorems.Thm_GlobalTheory_LocLift_isHolTo_mono
import Theorems.Thm_GlobalTheory_LocLift_linear_lift_unique
import Theorems.Thm_GlobalTheory_RiemannRel_differentiableOn_left_inverse
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_datum_free_int
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk
attribute [local simp] GlobalTheory.coe_symplecticGroupMap
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology
open GlobalTheory
open LocLift
set_option maxHeartbeats 400000
namespace GlobalTheory
namespace LocLift
theorem _root_.solution : ThetaUnifAV → Out.Laws → (∀ (k : Type) [Field
    k] (X : Scheme.{0}) (s
    : X ⟶ Sp k), Smooth s → IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
    : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p
    + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B'
    : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S'
    : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f
    : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap
    o' o f)) → (∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (G
    : Over X) [GrpObj G] (g m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀
    : Fin m → ℂ) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶
    G)), LocallyOfFiniteType s → IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ((∀ z w, e₀ (z
    + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀ ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧
    (∀ w, ∃! v : epsPt (y b₀) ⟶ G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y
    b₀) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀
    0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) → ∃ (B' : Set (Fin m → ℂ)) (e
    : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (r
    : ℝ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ e b₀ = e₀ ∧ 0 < r ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin
    m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ (∀ b ∈ B', ((∀ z w, (e b) (z + w) = (e b) z * (e
    b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧
    (∀ w, ∃! v : epsPt (y b) ⟶ G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b)
    z).left) w v.left)) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) ∧ ∀ (n : ℕ) (W : Set (Fin n → ℂ)) (β
    : (Fin n → ℂ) → (Fin m → ℂ)) (x : ∀ w, Over.mk (y (β w)) ⟶ G) (w₀ : Fin n → ℂ) (z₀
    : Fin g → ℂ), IsOpen W → w₀ ∈ W → DifferentiableOn ℂ β W → Set.MapsTo β W B' → IsHolTo W (fun w => (x
    w).left) → e (β w₀) z₀ = x w₀ → ∃ ζ : (Fin n → ℂ) → (Fin g →
    ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w) → (∀ (La
    : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (g m : ℕ) (B : Set (Fin m →
    ℂ)) (b₀ : Fin m → ℂ) (K : (Fin m → ℂ) → AddSubgroup (Fin g → ℂ)) (P : (Fin m → ℂ) → (La →+ (Fin
    g → ℂ))) (r : ℝ), IsOpen B → b₀ ∈ B → 0 < r → (∀ b ∈ B, ∀ z ∈ K b, ‖z‖ < r → z = 0) → (∀ (b
    : ℕ → (Fin m → ℂ)) (z : ℕ → (Fin g → ℂ)) (z₀ : Fin g → ℂ), Filter.Tendsto b Filter.atTop (nhds
    b₀) → Filter.Tendsto z Filter.atTop (nhds z₀) → (∀ i, z i ∈ K (b
    i)) → z₀ ∈ K b₀) → (∀ x, ContinuousAt (fun b => P b x) b₀) → (∀ b ∈ B, (P b).range ≤ K b) → (P
    b₀).range = K b₀ → Function.Injective (P b₀) → Submodule.span ℝ (Set.range (P
    b₀)) = ⊤ → ∀ᶠ b in nhds b₀, (P b).range = K b ∧ Function.Injective (P
    b) ∧ Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ DiscreteTopology (P b).range) → (∀ (O
    : Type) [CommRing O] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (F : (Fin m → ℂ) → (O →+*
    Matrix (Fin g) (Fin g) ℂ)) (ty : Fin g → (O →+* ℂ)), Module.Finite ℤ O → IsReduced (ℂ ⊗[ℤ]
    O) → IsOpen B → b₀ ∈ B → (∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B) → (∀ a, F b₀ a = Matrix.diagonal (fun i => ty i a)) → ∃ (B'
    : Set (Fin m → ℂ)) (h : (Fin m → ℂ) → Matrix (Fin g) (Fin
    g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ h b₀ = 1 ∧ (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B') ∧ ∀ b ∈ B', IsUnit (h
    b) ∧ ∀ a, F b a * h b = h b * Matrix.diagonal (fun i => ty i a)) → (∀ (X
    : Scheme.{0}) [IsLocallyNoetherian X] (P : Out.PolAV X) (m k : ℕ) (B : Set (Fin m → ℂ)) (y
    : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ P.A) (c : ℂˣ) (b₀
    : Fin m → ℂ), 0 < k → IsUnit (k : Γ(X,
    ⊤)) → IsOpen B → IsPreconnected B → b₀ ∈ B → IsHolTo B (fun b => (x
    b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ k = 1 ∧ x' b ^ k = 1) → ((x b₀ =
    x' b₀ → ∀ b ∈ B, x b = x' b) ∧ (Out.WeilIs P.A P.L k (x b₀) (x' b₀) (unitOn c) →
    ∀ b ∈ B, Out.WeilIs P.A P.L k (x b) (x' b) (unitOn c)))) → ∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g
    : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B
    : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (b₀ : Fin m → ℂ) (P₀ : D'.La →+ (Fin g →
    ℂ)) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶
    Xo.univ.t.G)), IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ((y b₀) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty P₀ ∧ ((∀ z w, e₀ (z + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀
    ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧ (∀ w, ∃! v : epsPt (y
    b₀) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y
    b₀) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀
    0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) ∧ (∀ z, e₀ z = 1 ↔ z ∈ (P₀).range)
    ∧ (∀ (a : 𝓞 E) z, e₀ (fun k => ty k (a : E) * z k) = e₀ z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a
    a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂
    : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e₀ ((k : ℂ)⁻¹ • P₀ a)) (e₀ ((k : ℂ)⁻¹ • P₀
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e₀ ((l.M : ℂ)⁻¹ • P₀ (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e₀ ((l.A : ℂ)⁻¹ • P₀ (t a))) → ∃ (B' : Set (Fin m → ℂ)) (P
    : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶
    Xo.univ.t.G)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ P b₀ = P₀ ∧ IsHolPeriods D' ty B' P ∧ IsHolTo (B'
    ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ ∀ b ∈ B', ((y b) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧
    Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y
    b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P
    b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e
    b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a))) := by
  intro hT hL hsm hpol _ hrel hLat hdiag hweil E _ _ _ H D l Xo σ g ty _ _ hty D' t m B y b₀ P₀ e₀ hB hb₀ hyσ hy
    ⟨_, ⟨q1, q2, _, q4, _⟩, he₀, k₀, l₀, w₀, η₀, ηA₀⟩
  obtain ⟨hab, hdim, hrig, hsym⟩ := hpol E H D l _ _ _ _ Xo.univ
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  haveI := (hsm _ _ Xo.s inferInstance).2.2
  haveI := hab.proper
  let A : Out.PolAV Xo.X :=
    { A := Xo.univ.t.G, isAb := hab, g := _, smoothDim := hdim, L := Xo.univ.t.PP.L, isLB := Xo.univ.t.PP.isLB,
      rigid := hrig, sym := hsym, ample := Xo.univ.ample, ktriv := Xo.univ.ktriv }
  rw [dim_eq H hty] at hdim
  obtain ⟨B₁, e, r, hB₁, hb₁, hB₁B, rfl, hr, hol, he, hl⟩ := hrel _ σ _ Xo.s Xo.univ.t.G g m B y b₀ e₀ inferInstance hab hdim
    hB hb₀ hyσ hy he₀
  change HasLifts B₁ y e at hl
  change ∀ b ∈ B₁, IsExp (y b) (e b) ∧ _ at he
  have hy₁ := isHolTo_mono hy hB₁ hB₁B
  obtain ⟨F, hF, hFd⟩ := exists_hol_rep hB₁ hb₁ hr hol he hl Xo.univ.t.act
  have hF₀ : ∀ a, F b₀ a = Matrix.diagonal (fun i => ((ty i).comp (algebraMap (𝓞 E) E)) a) := fun a =>
    Matrix.toLin'.injective (linear_lift_unique he₀.1 hr (he b₀ hb₁).2 fun z => by
      rw [Matrix.toLin'_apply, hF b₀ hb₁, ← l₀, Matrix.toLin'_apply]
      congr 1
      ext i
      rw [Matrix.mulVec_diagonal]
      rfl)
  obtain ⟨B₂, h, hB₂, hb₂, hB₂₁, hh₀, hhd, hh⟩ := hdiag (𝓞 E) g m B₁ b₀ F _ inferInstance (isReduced_complex_tensor E)
    hB₁ hb₁ hFd hF₀
  haveI := D'.fin
  haveI : Module.Finite ℤ D'.La := Module.Finite.trans (𝓞 E) D'.La
  haveI := datum_free_int D'
  obtain ⟨P, hP₀, hP⟩ := exists_periods hLat hB₁ hb₁ hy₁ hr hol he hl P₀ q2 q4 k₀
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hP.and (hB₂.mem_nhds hb₂))
  set C := Metric.ball b₀ ε
  have hCo : IsOpen C := Metric.isOpen_ball
  have hCc : IsPreconnected C := (convex_ball b₀ ε).isPreconnected
  have hC₀ : b₀ ∈ C := Metric.mem_ball_self hε
  have hC₂ : C ⊆ B₂ := fun b hb => (hball b hb).2
  have hC₁ : C ⊆ B₁ := hC₂.trans hB₂₁
  have hPd : ∀ x, DifferentiableOn ℂ (fun b => P b x) C := fun x b hb => ((hball b hb).1.1 x).differentiableWithinAt
  have hmv : ∀ {M : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
      {W : Set V} {β : V → (Fin m → ℂ)} {v : V → (Fin g → ℂ)}, (∀ i j, DifferentiableOn ℂ (fun w => M (β w) i j) W) →
      DifferentiableOn ℂ v W → DifferentiableOn ℂ (fun w => (M (β w)).mulVec (v w)) W := fun hM hv =>
    differentiableOn_pi.2 fun i => by
      simp only [Matrix.mulVec, dotProduct]
      exact DifferentiableOn.fun_sum fun j _ => (hM i j).fun_mul (differentiableOn_pi.1 hv j)
  have hk1 : ∀ b ∈ C, ∀ x, e b (P b x) = 1 := fun b hb x => ((hball b hb).1.2.1 _).2 ⟨x, rfl⟩
  have hlin : ∀ (a : 𝓞 E) x, ∀ b ∈ C, P b (a • x) - (F b a).mulVec (P b x) = 0 := fun a x => by
    refine eq_zero_of_small hCc ((hPd _).sub (hmv (M := fun b => F b a) (β := id)
      (fun i j => (hFd a i j).mono hC₁) (hPd x))).continuousOn hr (fun b hb hn => (he b (hC₁ hb)).2 _ hn ?_) hC₀ ?_
    · haveI := Xo.univ.t.act.hom a
      exact (hom_sub_eq_one (he b (hC₁ hb)).1.1).2 (by rw [hF b (hC₁ hb), hk1 b hb, hk1 b hb, MonObj.one_comp])
    · ext i
      simp [hP₀, hF₀, q1, Matrix.mulVec_diagonal]
  have htor : ∀ (k : ℕ) x, IsHolTo C (fun b => (e b ((k : ℂ)⁻¹ • P b x)).left) := fun k x =>
    isHolTo_comp (β := fun b => (b, (k : ℂ)⁻¹ • P b x)) hol hCo
      (differentiableOn_id.prodMk ((hPd x).fun_const_smul _)) fun b hb => ⟨hC₁ hb, trivial⟩
  have hpow : ∀ (k : ℕ), 0 < k → ∀ x, ∀ b ∈ C, e b ((k : ℂ)⁻¹ • P b x) ^ k = 1 := fun k hk x b hb => by
    rw [← hom_nsmul (he b (hC₁ hb)).1.1, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 hk.ne'),
      hk1 b hb]
  have hwe : ∀ b ∈ C, ∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) →
      Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e b ((k : ℂ)⁻¹ • P b a)) (e b ((k : ℂ)⁻¹ • P b a₂)) (unitOn c) :=
    fun b hb k a a₂ c hk hc => (hweil Xo.X A m k C y (fun b => e b ((k : ℂ)⁻¹ • P b a))
      (fun b => e b ((k : ℂ)⁻¹ • P b a₂)) c b₀ hk (isUnit_natCast_of_over Xo.s hk) hCo hCc hC₀ (htor k a) (htor k a₂)
      fun b hb => ⟨hpow k hk a b hb, hpow k hk a₂ b hb⟩).2 (by rw [hP₀]; exact w₀ k a a₂ c hk hc) b hb
  have hsec : ∀ (k : ℕ), 0 < k → ∀ (s : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) x, (∀ T, (toUnit T ≫ s) ^ k = 1) →
      toUnit _ ≫ s = e b₀ ((k : ℂ)⁻¹ • P₀ x) → ∀ b ∈ C, toUnit _ ≫ s = e b ((k : ℂ)⁻¹ • P b x) :=
    fun k hk s x hs h0 => (hweil Xo.X A m k C y (fun b => toUnit _ ≫ s)
      (fun b => e b ((k : ℂ)⁻¹ • P b x)) 1 b₀ hk (isUnit_natCast_of_over Xo.s hk) hCo hCc hC₀
      (isHolTo_congr (isHolTo_comp_hom (isHolTo_mono hy₁ hCo hC₁) s.left) fun b _ => by
        rw [Over.comp_left, Over.toUnit_left]; rfl) (htor k x)
      fun b hb => ⟨hs _, hpow k hk x b hb⟩).1 (by rw [hP₀]; exact h0)
  have hform : ∀ b ∈ C, HasForm D'.EF (P b) := fun b hb =>
    hasForm_of_weil hT hL.polBaseChange A (y b) (y b) (Category.id_comp _).symm (he b (hC₁ hb)).1 hr
      (he b (hC₁ hb)).2 (fun n x hx h0 => by
        obtain ⟨ζ, -, h2, h3⟩ := hl n Set.univ (fun _ => b) x 0 0 isOpen_univ trivial (differentiableOn_const _)
          (fun _ _ => hC₁ hb) hx h0
        exact ⟨ζ, h2, h3⟩) D'.EF (P b) (hk1 b hb) (hwe b hb)
  have hM := natCast_mem_level l
  obtain ⟨P', hP'd⟩ := exists_mulVec_comp (fun b => (h b)⁻¹) P
  have hdet : ∀ b ∈ C, IsUnit (h b).det := fun b hb => (Matrix.isUnit_iff_isUnit_det _).1 (hh b (hC₂ hb)).1
  have hP' : ∀ b ∈ C, ∀ x, (h b).mulVec (P' b x) = P b x := fun b hb x => by
    rw [hP'd, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hdet b hb), Matrix.one_mulVec]
  have hj : ∀ b ∈ C, ∃ j : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ), ∀ z, (h b).mulVec z = j z := fun b hb =>
    exists_equiv_mulVec (hdet b hb)
  have hFh : ∀ b ∈ C, ∀ (a : 𝓞 E) z, (h b).mulVec (fun k => ty k (a : E) * z k) = (F b a).mulVec ((h b).mulVec z) :=
    fun b hb a z => by
      rw [Matrix.mulVec_mulVec, (hh b (hC₂ hb)).2, ← Matrix.mulVec_mulVec]
      congr 1
      ext i
      rw [Matrix.mulVec_diagonal]
      rfl
  have hper : ∀ b ∈ C, IsPeriod D' ty (P' b) := fun b hb => by
    obtain ⟨j, hj⟩ := hj b hb
    have e1 : ∀ x, j (P' b x) = P b x := fun x => by rw [← hj, hP' b hb]
    obtain ⟨s1, s2⟩ := lattice_comp j e1 (hball b hb).1.2.2.2.1 (hball b hb).1.2.2.2.2
    refine ⟨fun a x i => congrFun (j.injective ?_ : P' b (a • x) = fun i => ty i (a : E) * P' b x i) i,
      fun x x' hx => (hball b hb).1.2.2.1 (by rw [← e1, hx, e1]), s2, s1,
      HasForm.of_comp j.toLinearEquiv.toLinearMap j.injective (by
        rw [show (fun x => j.toLinearEquiv.toLinearMap (P' b x)) = P b from funext e1]
        exact hform b hb)⟩
    rw [e1, ← hj, hFh b hb, hP' b hb]
    exact sub_eq_zero.1 (hlin a x b hb)
  refine ⟨C, P', fun b z => e b ((h b).mulVec z), hCo, hC₀, hC₁.trans hB₁B, ?_, ⟨hper, fun x => ?_⟩, ?_,
    fun b hb => ⟨hyσ b (hB₁B (hC₁ hb)), hper b hb, ?_, fun z => ?_, fun a z => ?_, ?_, fun a ha => ?_, fun a => ?_⟩⟩
  · ext1 x
    rw [← hP₀, ← hP' b₀ hC₀, hh₀, Matrix.one_mulVec]
  · simp only [hP'd]
    exact hmv (M := fun b => (h b)⁻¹) (β := id) (RiemannRel.differentiableOn_left_inverse h _
      (fun i j => (hhd i j).mono hC₂) fun b hb => Matrix.nonsing_inv_mul _ (hdet b hb)) (hPd x)
  · exact isHolTo_comp (β := fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (bz.1, (h bz.1).mulVec bz.2)) hol
      (hCo.prod isOpen_univ) (differentiableOn_fst.prodMk (hmv (β := Prod.fst)
        (fun i j => (hhd i j).comp differentiableOn_fst fun _ hw => hC₂ hw.1) differentiableOn_snd))
      fun _ hw => ⟨hC₁ hw.1, trivial⟩
  · obtain ⟨j, hj⟩ := hj b hb
    change IsExp (y b) (fun z => e b ((h b).mulVec z))
    simp only [hj]
    exact (he b (hC₁ hb)).1.comp j
  · obtain ⟨j, hj⟩ := hj b hb
    rw [(hball b hb).1.2.1]
    refine exists_congr fun x => ?_
    rw [← hP' b hb, hj, hj]
    exact j.injective.eq_iff
  · beta_reduce
    rw [hFh b hb, hF b (hC₁ hb)]
  · simpa only [Matrix.mulVec_smul, hP' b hb] using hwe b hb
  · simp only [Matrix.mulVec_smul, hP' b hb]
    refine hsec l.M (by have := l.three_le; omega) _ _ (section_pow Xo.univ.eta_add (Xo.univ.eta_ker _ ?_)) (η₀ a ha) b hb
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul hM trivial
  · simp only [Matrix.mulVec_smul, hP' b hb]
    exact hsec l.A l.A_pos _ _ (section_pow Xo.univ.etaA_add (Xo.univ.etaA_ker a)) (ηA₀ a) b hb
end LocLift
end GlobalTheory
