-- Prove2me | solution 1 for GlobalTheory.AbelianExp.exists_holUnif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:44:08.613245+00:00
-- url     : https://prove2.me/submissions/714c5aa0-5e87-47b6-9a5e-e449beb6f1dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ContinuousOnValue
import Theorems.Thm_GlobalTheory_AbelianExp_HolOn_const
import Theorems.Thm_GlobalTheory_AbelianExp_HolOn_comp
import Theorems.Thm_GlobalTheory_AbelianExp_HolOn_post
import Theorems.Thm_GlobalTheory_AbelianExp_HolOn_of_local
import Theorems.Thm_GlobalTheory_AbelianExp_HolOn_analyticAt
import Theorems.Thm_GlobalTheory_IsAnalyticGroupChart_analyticAt_chart_exp
import Theorems.Thm_GlobalTheory_IsAnalyticGroupChart_exp_log
import Theorems.Thm_GlobalTheory_IsAnalyticGroupChart_exp_surjective
import Theorems.Thm_GlobalTheory_IsAnalyticGroupChart_hasFDerivAt_chart_exp
import Theorems.Thm_GlobalTheory_IsAnalyticGroupChart_log_exp
import Theorems.Thm_GlobalTheory_IsAnalyticGroupChart_mem_periodLattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.AbelianExp
attribute [local instance] pointTopology
namespace GlobalTheory.AbelianExp
theorem _root_.solution :
    Out.MulNSt → (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (X Y : Over (Sp ℂ)) (a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (b : E → (𝟙_ (Over (Sp ℂ)) ⟶ Y)), (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → (∀ (U : (Y).left.Opens) (f : Γ((Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (b w).left U f) {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U}) → (∀ (U : (X ⊗ Y).left.Opens) (f : Γ((X ⊗ Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' ((fun w => lift (a w) (b w)) w).left U f) {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U})) → (∀ (A : Over (Sp ℂ)) [GrpObj A], @IsTopologicalGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) (TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ A) | ∃ (U : A.left.Opens) (f : Γ(A.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}) _) → (∀ P : Out.PolAV (Sp ℂ), @CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ P.A) (TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ P.A) | ∃ (U : P.A.left.Opens) (f : Γ(P.A.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}})) → (∀ (X : Over (Sp ℂ)) (g : ℕ), SmoothOfRelativeDimension g X.hom → ∀ e : (𝟙_ (Over (Sp ℂ)) ⟶ X), ∃ (W : Set (Fin g → ℂ)) (σ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (U : X.left.Opens) (t : Fin g → Γ(X.left, U)), IsOpen W ∧ 0 ∈ W ∧ σ 0 = e ∧ IsAffineOpen U ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (σ w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (σ w).left U f) {w | w ∈ W ∧ ⊤ ≤ (σ w).left ⁻¹ᵁ U}) ∧ (∀ w ∈ W, ⊤ ≤ (σ w).left ⁻¹ᵁ U ∧ ∀ i, valAt' (σ w).left U (t i) = w i) ∧ IsOpen[(TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ X) | ∃ (U : X.left.Opens) (f : Γ(X.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}})] (σ '' W) ∧ (∀ D : Γ(X.left, U) →+ ℂ, (∀ a, D (constFn X.hom U a) = 0) → (∀ f f', D (f * f') = valAt' e.left U f * D f' + valAt' e.left U f' * D f) → (∀ i, D (t i) = 0) → D = 0)) → (∀ P : Out.PolAV (Sp ℂ), ∃ u : HolUnif P.A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ : LB P.A.left) P.g, (∃ (U : P.A.left.Opens) (t : Fin P.g → Γ(P.A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(P.A.left, U) →+ ℂ, (∀ a, D (constFn P.A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin P.g → ℂ)) 0) ∧ (∀ (n : ℕ) (a : (Fin n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), (∀ (U : (P.A).left.Opens) (f : Γ((P.A).left, U)), IsOpen {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → a 0 = 1 → ∃ G : (Fin n → ℂ) → (Fin P.g → ℂ), G 0 = 0 ∧ AnalyticAt ℂ G 0 ∧ ∀ᶠ w in 𝓝 0, u.ex (G w) = a w)) := by
  intro hmul H1 H2 H3 H4 H5 P
  haveI : IsCommMonObj P.A := P.isAb.comm
  have hval : ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X) (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens)
      (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f :=
    fun X x => (H1 X x).2.2.2.1
  haveI hTG : IsTopologicalGroup (𝟙_ (Over (Sp ℂ)) ⟶ P.A) := H3 P.A
  haveI : IsTopologicalAddGroup (Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) := inferInstance
  haveI : CompactSpace (Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) := H4 P
  obtain ⟨W, σ, U, t, hW, h0W, hσ0, hUa, hσ, ht, ho, hD⟩ := H5 P.A P.g P.smoothDim 1
  have hσ' : HolOn W σ := hσ
  have hmulHol : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W' : Set E}
      {a b : E → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)}, HolOn W' a → HolOn W' b →
        HolOn W' fun w => a w * b w := by
    intro E _ _ W' a b ha hb
    have hl : HolOn W' fun w => lift (a w) (b w) := H2 E W' P.A P.A a b ha hb
    have := hl.post hval μ[P.A]
    simpa only [Hom.mul_def] using this
  let φ' : OpenPartialHomeomorph (Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (Fin P.g → ℂ) :=
    chart t hW hσ' ht ho
  have hσ00 : (fun i => valAt' (σ 0).left U (t i)) = 0 := funext fun i => (ht 0 h0W).2 i
  have hφ : IsAnalyticGroupChart φ' := by
    refine ⟨⟨0, h0W, hσ0⟩, ?_, ?_⟩
    · show (fun i => valAt' ((1 : 𝟙_ (Over (Sp ℂ)) ⟶ P.A)).left U (t i)) = 0
      rw [← hσ0]
      exact hσ00
    · have hprod : HolOn (W ×ˢ W) fun p : (Fin P.g → ℂ) × (Fin P.g → ℂ) => σ p.1 * σ p.2 :=
        hmulHol (hσ'.comp (hW.prod hW) differentiableOn_fst (fun p hp => hp.1))
          (hσ'.comp (hW.prod hW) differentiableOn_snd (fun p hp => hp.2))
      have h00 : σ (0 : (Fin P.g → ℂ) × (Fin P.g → ℂ)).1 * σ (0 : (Fin P.g → ℂ) × (Fin P.g → ℂ)).2
          = σ 0 := by simp [hσ0]
      have hU0 : ⊤ ≤ (σ (0 : (Fin P.g → ℂ) × (Fin P.g → ℂ)).1 *
          σ (0 : (Fin P.g → ℂ) × (Fin P.g → ℂ)).2).left ⁻¹ᵁ U := by
        rw [h00]
        exact (ht 0 h0W).1
      exact hprod.analyticAt t ⟨h0W, h0W⟩ hU0
  have hdiv : ∀ n : ℕ, n ≠ 0 → ∀ a : Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A), ∃ b, n • b = a := by
    intro n hn a
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    obtain ⟨hfin, -, hsur, -⟩ := hmul (Sp ℂ) P n hn1
    haveI : Smooth P.A.hom := P.isAb.smooth
    haveI : LocallyOfFiniteType P.A.hom := inferInstance
    haveI : JacobsonSpace P.A.left := LocallyOfFiniteType.jacobsonSpace P.A.hom
    set y : 𝟙_ (Over (Sp ℂ)) ⟶ P.A := Additive.toMul a with hy
    have hyh : y.left ≫ P.A.hom = 𝟙 _ := Over.w y
    have hp : y.left (IsLocalRing.closedPoint ℂ) ∈ closedPoints P.A.left :=
      ((pointEquivClosedPoint P.A.hom) ⟨y.left, hyh⟩).2
    obtain ⟨q, hqZ, hqc⟩ := nonempty_inter_closedPoints
      (Z := (Out.mulA P.A n).left ⁻¹' {y.left (IsLocalRing.closedPoint ℂ)})
      (hsur.surj _) ((IsClosed.preimage (Out.mulA P.A n).left.continuous hp).isLocallyClosed)
    have hb'h : pointOfClosedPoint P.A.hom q hqc ≫ P.A.hom = 𝟙 _ :=
      pointOfClosedPoint_comp P.A.hom q hqc
    let b : 𝟙_ (Over (Sp ℂ)) ⟶ P.A := Over.homMk (pointOfClosedPoint P.A.hom q hqc) hb'h
    refine ⟨Additive.ofMul b, ?_⟩
    rw [← ofMul_pow]
    show Additive.ofMul (b ^ n) = Additive.ofMul y
    congr 1
    apply Over.OverMorphism.ext
    have hpow : b ≫ Out.mulA P.A n = b ^ n := by
      unfold Out.mulA
      rw [MonObj.comp_pow, Category.comp_id]
    rw [← hpow, Over.comp_left]
    refine ext_of_apply_closedPoint_eq P.A.hom ?_ hyh ?_
    · rw [Category.assoc, Over.w (Out.mulA P.A n)]
      exact hb'h
    · show (Out.mulA P.A n).left (pointOfClosedPoint P.A.hom q hqc (IsLocalRing.closedPoint ℂ)) = _
      have h2 := pointOfClosedPoint_apply P.A.hom q hqc (IsLocalRing.closedPoint ℂ)
      exact (congrArg (Out.mulA P.A n).left h2).trans hqZ
  have hsurj := hφ.exp_surjective hdiv
  have hex0 : Additive.toMul (hφ.exp 0) = σ 0 := by
    rw [hσ0, map_zero]
    rfl

  have hloc : ∃ N : Set (Fin P.g → ℂ), IsOpen N ∧ (0 : Fin P.g → ℂ) ∈ N ∧
      HolOn N (fun v => σ (φ' (hφ.exp v))) ∧
      ∀ v ∈ N, Additive.toMul (hφ.exp v) = σ (φ' (hφ.exp v)) := by
    have hc := hφ.analyticAt_chart_exp
    have hc0 : φ' (hφ.exp 0) = 0 := by rw [map_zero]; exact hφ.map_zero
    have hsrc : ∀ᶠ v in 𝓝 (0 : Fin P.g → ℂ), hφ.exp v ∈ φ'.source := by
      have h1 := hφ.continuous_exp.tendsto 0
      rw [map_zero] at h1
      exact h1.eventually (φ'.open_source.mem_nhds hφ.zero_mem_source)
    have hW0 : ∀ᶠ v in 𝓝 (0 : Fin P.g → ℂ), φ' (hφ.exp v) ∈ W :=
      hc.continuousAt.preimage_mem_nhds (by rw [hc0]; exact hW.mem_nhds h0W)
    obtain ⟨N, hNp, hNo, hN0⟩ := eventually_nhds_iff.1 (hc.eventually_analyticAt.and (hsrc.and hW0))
    refine ⟨N, hNo, hN0, ?_, ?_⟩
    · exact hσ'.comp hNo (fun v hv => (hNp v hv).1.differentiableAt.differentiableWithinAt)
        (fun v hv => (hNp v hv).2.2)
    · intro v hv
      exact (φ'.left_inv (hNp v hv).2.1).symm
  obtain ⟨N, hNo, hN0, hNhol, hNeq⟩ := hloc
  refine ⟨{ ex := fun z => Additive.toMul (hφ.exp z)
            ex_add := fun z w => by
              show Additive.toMul (hφ.exp (z + w)) = _
              rw [map_add]
              rfl
            ex_onto := fun y => by
              obtain ⟨z, hz⟩ := hsurj (Additive.ofMul y)
              exact ⟨z, by show Additive.toMul (hφ.exp z) = y; rw [hz]; rfl⟩
            Λ := hφ.periodLattice
            ker := fun z => by
              rw [hφ.mem_periodLattice]
              exact Iff.rfl
            discrete := inferInstance
            full := (inferInstance : IsZLattice ℝ hφ.periodLattice).span_top
            hol := ?_
            fr := fun _ _ => 1
            fr_hol := fun _ => differentiableOn_const _
            fr_ne := fun _ _ _ => one_ne_zero
            fr_compat := ?_ }, ?_, ?_⟩
  · intro U' f
    refine HolOn.of_local (fun z0 => ?_) U' f
    refine ⟨(fun z => z - z0) ⁻¹' N, fun z => Additive.toMul (hφ.exp z0) * σ (φ' (hφ.exp (z - z0))),
      by simpa using hN0, ?_, ?_⟩
    · exact hmulHol (HolOn.const (hNo.preimage (continuous_sub_right z0)) _)
        (hNhol.comp (hNo.preimage (continuous_sub_right z0))
          (differentiableOn_id.sub_const z0) (fun z hz => hz))
    · have ht0 : Tendsto (fun z => z - z0) (𝓝 z0) (𝓝 0) := by
        have := (continuous_sub_right z0).tendsto z0
        rwa [sub_self] at this
      filter_upwards [ht0.eventually (hNo.mem_nhds hN0)] with z hz
      rw [← hNeq _ hz]
      show Additive.toMul (hφ.exp z) = Additive.toMul (hφ.exp z0) * Additive.toMul (hφ.exp (z - z0))
      rw [← toMul_add, ← map_add, add_sub_cancel]
  · intro i j z hz
    obtain ⟨e, he⟩ := (H1 _ (Additive.toMul (hφ.exp z)).left).2.1 _ hz
    rw [he]
    simp
  · refine ⟨U, t, hUa, ?_, ?_, ?_⟩
    · show ⊤ ≤ (Additive.toMul (hφ.exp 0)).left ⁻¹ᵁ U
      rw [hex0]
      exact (ht 0 h0W).1
    · have h1 : Additive.toMul (hφ.exp 0) = 1 := by rw [hex0, hσ0]
      intro D
      dsimp only
      rw [h1]
      exact hD D
    · exact hφ.hasFDerivAt_chart_exp
  · intro n a ha ha0
    have haH : HolOn Set.univ a := ha
    have hU1 : ⊤ ≤ (a 0).left ⁻¹ᵁ U := by
      rw [ha0, ← hσ0]
      exact (ht 0 h0W).1
    have hc : AnalyticAt ℂ (fun w i => valAt' (a w).left U (t i)) 0 :=
      haH.analyticAt t (Set.mem_univ 0) hU1
    have hca : (fun i => valAt' (a 0).left U (t i)) = 0 := by
      rw [ha0, ← hσ0]
      exact hσ00
    have hlog0 : hφ.log 0 = 0 := by
      have := hφ.log_exp.self_of_nhds
      rw [map_zero, hφ.map_zero] at this
      exact this
    refine ⟨fun w => hφ.log (φ' (Additive.ofMul (a w))), ?_, ?_, ?_⟩
    · show hφ.log (fun i => valAt' (a 0).left U (t i)) = 0
      rw [hca]
      exact hlog0
    · exact AnalyticAt.comp_of_eq hφ.isLocalCommGroupLaw.analyticAt_log hc hca
    · have hcont : Tendsto (fun w => Additive.ofMul (a w)) (𝓝 0)
          (𝓝 (0 : Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A))) := by
        have := haH.continuousAt (Set.mem_univ (0 : Fin n → ℂ))
        rw [ContinuousAt, ha0] at this
        exact this
      filter_upwards [hcont.eventually hφ.exp_log] with w hw
      exact congrArg Additive.toMul hw
end GlobalTheory.AbelianExp
