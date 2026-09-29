-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_gauge_whittakerLoc_of_isGaugeMajorised3_of_form_ne_zero_of_isCubicInductionDataOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/cc7fb943-59a8-5d60-aa88-5bb3c83f876e

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_gauge_whittakerLoc_of_isGaugeMajorised3_of_form_ne_zero_of_isCubicInductionDataOn

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction

noncomputable section

namespace KcLocalGauge

section Components

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem componentAt3_localToAdelic3_self (x : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ v (localToAdelic3 v x) = x := by
  refine Units.ext ?_
  show ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
      (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v x)) = x
  rw [show ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
        (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v x)) =
      (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
        (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v x))) from by
      ext i j; rfl,
    mapMatrix_fin_finMatN, mapMatrix_localMatN_self]

theorem componentAt3_localToAdelic3_of_ne {v w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) (x : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ w (localToAdelic3 v x) = 1 := by
  refine Units.ext ?_
  show ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
      (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v x)) = 1
  rw [show ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
        (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v x)) =
      (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
        (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v x))) from by
      ext i j; rfl,
    mapMatrix_fin_finMatN, mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ v _ hw]

theorem archComponent3_localToAdelic3 (x : LocalGL3 v) :
    archComponent3 (𝓞 ℚ) ℚ (localToAdelic3 v x) = 1 := by
  refine Units.ext ?_
  show (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v x)) = 1
  rw [mapMatrix_arch_finMatN]

theorem componentAt3_apply (w : HeightOneSpectrum (𝓞 ℚ)) (Y : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    ((componentAt3 (𝓞 ℚ) ℚ w Y : LocalGL3 w) : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ)) i j =
      ((Y : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 w := rfl

theorem finite_setOf_not_mem_localMaximalCompact3 (Y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    {w : HeightOneSpectrum (𝓞 ℚ) | componentAt3 (𝓞 ℚ) ℚ w Y ∉ localMaximalCompact3 (𝓞 ℚ) ℚ w}.Finite := by
  have hent : ∀ (Z : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3),
      {w : HeightOneSpectrum (𝓞 ℚ) | ((Z : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 w ∉
        w.adicCompletionIntegers ℚ}.Finite :=
    fun Z i j => Filter.eventually_cofinite.1 ((Z : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2.2
  refine (((Set.finite_iUnion fun i => Set.finite_iUnion fun j => hent Y i j)).union
    (Set.finite_iUnion fun i => Set.finite_iUnion fun j => hent Y⁻¹ i j)).subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq, mem_localMaximalCompact3_iff, not_and_or, not_forall] at hw
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq]
  rcases hw with ⟨i, j, h⟩ | ⟨i, j, h⟩
  · refine Or.inl ⟨i, j, fun hint => h ?_⟩
    rw [componentAt3_apply]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hint
  · refine Or.inr ⟨i, j, fun hint => h ?_⟩
    rw [← map_inv, componentAt3_apply]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hint

end Components

section Replace

variable (v : HeightOneSpectrum (𝓞 ℚ)) (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ)

def replaceAt (h : LocalGL3 v) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  g₀ * localToAdelic3 v ((componentAt3 (𝓞 ℚ) ℚ v g₀)⁻¹ * h)

theorem componentAt3_replaceAt_self (h : LocalGL3 v) : componentAt3 (𝓞 ℚ) ℚ v (replaceAt v g₀ h) = h := by
  rw [replaceAt, map_mul, componentAt3_localToAdelic3_self, mul_inv_cancel_left]

theorem componentAt3_replaceAt_of_ne {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) (h : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ w (replaceAt v g₀ h) = componentAt3 (𝓞 ℚ) ℚ w g₀ := by
  rw [replaceAt, map_mul, componentAt3_localToAdelic3_of_ne hw, mul_one]

theorem archComponent3_replaceAt (h : LocalGL3 v) :
    archComponent3 (𝓞 ℚ) ℚ (replaceAt v g₀ h) = archComponent3 (𝓞 ℚ) ℚ g₀ := by
  rw [replaceAt, map_mul, archComponent3_localToAdelic3, mul_one]

theorem replaceAt_componentAt3 : replaceAt v g₀ (componentAt3 (𝓞 ℚ) ℚ v g₀) = g₀ := by
  rw [replaceAt, inv_mul_cancel, map_one, mul_one]

theorem finRoot₁_replaceAt_self (h : LocalGL3 v) :
    finRoot₁ ℚ v (replaceAt v g₀ h) = detSize h * lastRowSup h / minorSup h ^ 2 := by
  rw [finRoot₁, componentAt3_replaceAt_self]

theorem finRoot₂_replaceAt_self (h : LocalGL3 v) :
    finRoot₂ ℚ v (replaceAt v g₀ h) = minorSup h / lastRowSup h ^ 2 := by
  rw [finRoot₂, componentAt3_replaceAt_self]

theorem finRoot₁_replaceAt_of_ne {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) (h : LocalGL3 v) :
    finRoot₁ ℚ w (replaceAt v g₀ h) = finRoot₁ ℚ w g₀ := by
  rw [finRoot₁, finRoot₁, componentAt3_replaceAt_of_ne v g₀ hw]

theorem finRoot₂_replaceAt_of_ne {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) (h : LocalGL3 v) :
    finRoot₂ ℚ w (replaceAt v g₀ h) = finRoot₂ ℚ w g₀ := by
  rw [finRoot₂, finRoot₂, componentAt3_replaceAt_of_ne v g₀ hw]

theorem archPlaceComponent3_replaceAt (w : InfinitePlace ℚ) (h : LocalGL3 v) :
    archPlaceComponent3 ℚ w (replaceAt v g₀ h) = archPlaceComponent3 ℚ w g₀ := by
  show Matrix.GeneralLinearGroup.map (AdelicLevel.archEval ℚ w) (archComponent3 (𝓞 ℚ) ℚ (replaceAt v g₀ h)) =
    Matrix.GeneralLinearGroup.map (AdelicLevel.archEval ℚ w) (archComponent3 (𝓞 ℚ) ℚ g₀)
  rw [archComponent3_replaceAt]

theorem archRoot₁_replaceAt (w : InfinitePlace ℚ) (h : LocalGL3 v) :
    archRoot₁ ℚ w (replaceAt v g₀ h) = archRoot₁ ℚ w g₀ := by
  simp only [archRoot₁, archPlaceComponent3_replaceAt]

theorem archRoot₂_replaceAt (w : InfinitePlace ℚ) (h : LocalGL3 v) :
    archRoot₂ ℚ w (replaceAt v g₀ h) = archRoot₂ ℚ w g₀ := by
  simp only [archRoot₂, archPlaceComponent3_replaceAt]

theorem archRootSum_replaceAt (h : LocalGL3 v) : archRootSum ℚ (replaceAt v g₀ h) = archRootSum ℚ g₀ := by
  simp only [archRootSum, archRoot₁_replaceAt, archRoot₂_replaceAt]

theorem inRootLevel_replaceAt_iff (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (B : ℝ) (h₀ : InRootLevel ℚ T B g₀)
    (Bv : ℝ) (hBv₁ : v ∈ T → Bv = B) (hBv₂ : v ∉ T → Bv = 1) (h : LocalGL3 v) :
    InRootLevel ℚ T B (replaceAt v g₀ h) ↔
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ Bv ∧ minorSup h / lastRowSup h ^ 2 ≤ Bv) := by
  constructor
  · intro H
    by_cases hv : v ∈ T
    · rw [hBv₁ hv, ← finRoot₁_replaceAt_self v g₀ h, ← finRoot₂_replaceAt_self v g₀ h]
      exact H.2 v hv
    · rw [hBv₂ hv, ← finRoot₁_replaceAt_self v g₀ h, ← finRoot₂_replaceAt_self v g₀ h]
      exact H.1 v hv
  · intro H
    have key : ∀ X : ℝ, (detSize h * lastRowSup h / minorSup h ^ 2 ≤ X ∧ minorSup h / lastRowSup h ^ 2 ≤ X) →
        finRoot₁ ℚ v (replaceAt v g₀ h) ≤ X ∧ finRoot₂ ℚ v (replaceAt v g₀ h) ≤ X := fun X HX => by
      rwa [finRoot₁_replaceAt_self, finRoot₂_replaceAt_self]
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rcases eq_or_ne w v with hwv | hwv
      · have hv : v ∉ T := hwv ▸ hw
        rw [hwv]
        exact key _ (by rwa [hBv₂ hv] at H)
      · rw [finRoot₁_replaceAt_of_ne v g₀ hwv, finRoot₂_replaceAt_of_ne v g₀ hwv]
        exact h₀.1 w hw
    · rcases eq_or_ne w v with hwv | hwv
      · have hv : v ∈ T := hwv ▸ hw
        rw [hwv]
        exact key _ (by rwa [hBv₁ hv] at H)
      · rw [finRoot₁_replaceAt_of_ne v g₀ hwv, finRoot₂_replaceAt_of_ne v g₀ hwv]
        exact h₀.2 w hw

theorem finRootFam_replaceAt_of_ne {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) (h : LocalGL3 v) :
    finRoot₁ ℚ w (replaceAt v g₀ h) * finRoot₂ ℚ w (replaceAt v g₀ h) = finRoot₁ ℚ w g₀ * finRoot₂ ℚ w g₀ := by
  rw [finRoot₁_replaceAt_of_ne v g₀ hw, finRoot₂_replaceAt_of_ne v g₀ hw]

theorem mulSupport_subset (h : LocalGL3 v) :
    Function.mulSupport (fun w => finRoot₁ ℚ w (replaceAt v g₀ h) * finRoot₂ ℚ w (replaceAt v g₀ h)) ⊆
      insert v (Function.mulSupport fun w => finRoot₁ ℚ w g₀ * finRoot₂ ℚ w g₀) := by
  intro w hw
  by_cases hwv : w = v
  · rw [hwv]; exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ ?_
    rwa [Function.mem_mulSupport, ← finRootFam_replaceAt_of_ne v g₀ hwv h]

theorem mulSupport_subset' (h : LocalGL3 v) :
    (Function.mulSupport fun w => finRoot₁ ℚ w g₀ * finRoot₂ ℚ w g₀) ⊆
      insert v (Function.mulSupport (fun w => finRoot₁ ℚ w (replaceAt v g₀ h) * finRoot₂ ℚ w (replaceAt v g₀ h))) := by
  intro w hw
  by_cases hwv : w = v
  · rw [hwv]; exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ ?_
    rwa [Function.mem_mulSupport, finRootFam_replaceAt_of_ne v g₀ hwv h]

theorem rootSizeProd_replaceAt_of_finite
    (hfin : (Function.mulSupport fun w => finRoot₁ ℚ w g₀ * finRoot₂ ℚ w g₀).Finite) :
    ∃ P : ℝ, ∀ h : LocalGL3 v,
      rootSizeProd ℚ (replaceAt v g₀ h) =
        (detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2) * P := by
  classical
  set S₀ : Finset (HeightOneSpectrum (𝓞 ℚ)) := insert v hfin.toFinset with hS₀
  refine ⟨(∏ w ∈ S₀.erase v, finRoot₁ ℚ w g₀ * finRoot₂ ℚ w g₀) *
    ∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g₀ * archRoot₂ ℚ w g₀, fun h => ?_⟩
  have hsub : (Function.mulSupport fun w => finRoot₁ ℚ w (replaceAt v g₀ h) * finRoot₂ ℚ w (replaceAt v g₀ h)) ⊆
      (S₀ : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    refine (mulSupport_subset v g₀ h).trans ?_
    rw [hS₀, Finset.coe_insert, Set.Finite.coe_toFinset]
  rw [rootSizeProd, finprod_eq_prod_of_mulSupport_subset _ hsub, ← Finset.mul_prod_erase S₀ _ (Finset.mem_insert_self v _),
    finRoot₁_replaceAt_self, finRoot₂_replaceAt_self]
  have hprod : ∏ w ∈ S₀.erase v, finRoot₁ ℚ w (replaceAt v g₀ h) * finRoot₂ ℚ w (replaceAt v g₀ h) =
      ∏ w ∈ S₀.erase v, finRoot₁ ℚ w g₀ * finRoot₂ ℚ w g₀ :=
    Finset.prod_congr rfl fun w hw => finRootFam_replaceAt_of_ne v g₀ (Finset.ne_of_mem_erase hw) h
  rw [hprod]
  simp only [archRoot₁_replaceAt, archRoot₂_replaceAt]
  ring

theorem rootSizeProd_replaceAt_of_infinite
    (hinf : (Function.mulSupport fun w => finRoot₁ ℚ w g₀ * finRoot₂ ℚ w g₀).Infinite) (h : LocalGL3 v) :
    rootSizeProd ℚ (replaceAt v g₀ h) = ∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g₀ * archRoot₂ ℚ w g₀ := by
  have hinf' : (Function.mulSupport fun w => finRoot₁ ℚ w (replaceAt v g₀ h) * finRoot₂ ℚ w (replaceAt v g₀ h)).Infinite :=
    fun hf => hinf ((hf.insert v).subset (mulSupport_subset' v g₀ h))
  rw [rootSizeProd, finprod_of_infinite_mulSupport hinf', one_mul]
  simp only [archRoot₁_replaceAt, archRoot₂_replaceAt]

end Replace

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

theorem main
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (S : Set (HeightOneSpectrum (𝓞 ℚ))) (X : CubicInductionData) (hX : IsCubicInductionDataOn K pins ψ μ S X)
    (hF0 : X.form ≠ 0) (hFg : IsGaugeMajorised3 ℚ X.whittaker)
    (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → p ∉ S)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) →
        X.whittakerLoc v h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖X.whittakerLoc v h‖ ≤
          C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t) := by
  classical

  obtain ⟨g₀, hg₀⟩ : ∃ g : AdelicGL 3 (𝓞 ℚ) ℚ, X.whittaker g ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hF0
    funext g
    have hz : (fun i : MirabolicIndex ℚ => X.whittaker (mirabolicTranslate i * g)) = fun _ => 0 :=
      funext fun i => hall _
    have h := hX.expansion g
    rw [hz] at h
    exact h.unique hasSum_zero

  set T : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
    S' ∪ {v} ∪ (finite_setOf_not_mem_localMaximalCompact3 g₀).toFinset with hT
  have hTbad : ∀ w, w ∈ S → w ∈ T := by
    intro w hw
    have hwS : w ∈ S' := by
      by_contra h
      exact hgood w h hw
    rw [hT]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hwS)
  have hvT : v ∈ T := by
    rw [hT]; exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self v))
  have hint : ∀ (h : LocalGL3 v) (w : HeightOneSpectrum (𝓞 ℚ)), w ∉ T →
      componentAt3 (𝓞 ℚ) ℚ w (replaceAt v g₀ h) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w := by
    intro h w hw
    have hwv : w ≠ v := fun hwv => hw (hwv ▸ hvT)
    rw [componentAt3_replaceAt_of_ne v g₀ hwv]
    by_contra hnot
    apply hw
    rw [hT]
    exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 hnot)

  set c : ℂ := X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g₀) *
    ∏ w ∈ T.erase v, X.whittakerLoc w (componentAt3 (𝓞 ℚ) ℚ w g₀) with hc
  have hfac : ∀ h : LocalGL3 v, X.whittaker (replaceAt v g₀ h) = c * X.whittakerLoc v h := by
    intro h
    rw [hX.factorizable (replaceAt v g₀ h) T hTbad (hint h), archComponent3_replaceAt,
      ← Finset.mul_prod_erase T _ hvT, componentAt3_replaceAt_self]
    have hprod : ∏ w ∈ T.erase v, X.whittakerLoc w (componentAt3 (𝓞 ℚ) ℚ w (replaceAt v g₀ h)) =
        ∏ w ∈ T.erase v, X.whittakerLoc w (componentAt3 (𝓞 ℚ) ℚ w g₀) :=
      Finset.prod_congr rfl fun w hw => by rw [componentAt3_replaceAt_of_ne v g₀ (Finset.ne_of_mem_erase hw)]
    rw [hprod, hc]
    ring
  have hc0 : c ≠ 0 := by
    intro h0
    apply hg₀
    rw [← replaceAt_componentAt3 v g₀, hfac, h0, zero_mul]
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc0
  have hloc : ∀ h : LocalGL3 v, X.whittakerLoc v h = c⁻¹ * X.whittaker (replaceAt v g₀ h) := fun h => by
    rw [hfac, inv_mul_cancel_left₀ hc0]

  obtain ⟨t, Tg, B, hG⟩ := hFg
  obtain ⟨C, hC⟩ := hG 0
  have hlevel₀ : InRootLevel ℚ Tg B g₀ := by
    by_contra hnot
    exact hg₀ ((hC g₀).1 hnot)
  set Bv : ℝ := if v ∈ Tg then B else 1 with hBv
  have hBv₁ : v ∈ Tg → Bv = B := fun hv => by rw [hBv, if_pos hv]
  have hBv₂ : v ∉ Tg → Bv = 1 := fun hv => by rw [hBv, if_neg hv]

  have hsupp : ∀ h : LocalGL3 v,
      ¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ Bv ∧ minorSup h / lastRowSup h ^ 2 ≤ Bv) →
        X.whittakerLoc v h = 0 := by
    intro h hnot
    rw [hloc h, (hC (replaceAt v g₀ h)).1 (fun H => hnot ((inRootLevel_replaceAt_iff v g₀ Tg B hlevel₀ Bv hBv₁ hBv₂ h).1 H)),
      mul_zero]

  have hbound : ∀ h : LocalGL3 v,
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ Bv ∧ minorSup h / lastRowSup h ^ 2 ≤ Bv) →
        ‖X.whittakerLoc v h‖ ≤ C / rootSizeProd ℚ (replaceAt v g₀ h) ^ t / ‖c‖ := by
    intro h H
    have hlev : InRootLevel ℚ Tg B (replaceAt v g₀ h) := (inRootLevel_replaceAt_iff v g₀ Tg B hlevel₀ Bv hBv₁ hBv₂ h).2 H
    have hb := (hC (replaceAt v g₀ h)).2 hlev
    rw [pow_zero, mul_one] at hb
    rw [hloc h, norm_mul, norm_inv, mul_comm, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right hb hcpos.le
  by_cases hfin : (Function.mulSupport fun w => finRoot₁ ℚ w g₀ * finRoot₂ ℚ w g₀).Finite
  · obtain ⟨P, hP⟩ := rootSizeProd_replaceAt_of_finite v g₀ hfin
    refine ⟨Bv, t, C / (P ^ t * ‖c‖), fun h => ⟨hsupp h, fun H => ?_⟩⟩
    refine (hbound h H).trans (le_of_eq ?_)
    rw [hP h, mul_pow, div_div, mul_assoc, div_mul_eq_div_div_swap]
  · refine ⟨Bv, 0, C / (∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g₀ * archRoot₂ ℚ w g₀) ^ t / ‖c‖,
      fun h => ⟨hsupp h, fun H => ?_⟩⟩
    refine (hbound h H).trans (le_of_eq ?_)
    rw [rootSizeProd_replaceAt_of_infinite v g₀ hfin h, pow_zero, div_one]

end KcLocalGauge

theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (S : Set (HeightOneSpectrum (𝓞 ℚ))) (X : CubicInductionData) (hX : IsCubicInductionDataOn K pins ψ μ S X)
    (hF0 : X.form ≠ 0) (hFg : IsGaugeMajorised3 ℚ X.whittaker)
    (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → p ∉ S)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) →
        X.whittakerLoc v h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖X.whittakerLoc v h‖ ≤
          C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t) :=
  KcLocalGauge.main K pins ψ μ S X hX hF0 hFg S' hgood v

end
end S_LanglandsTunnell_CubicInduction_exists_gauge_whittakerLoc_of_isGaugeMajorised3_of_form_ne_zero_of_isCubicInductionDataOn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_gauge_whittakerLoc_of_isGaugeMajorised3_of_form_ne_zero_of_isCubicInductionDataOn (solution)
