-- Prove2me | solution 1 for MasulloGRH.zetaIntegral_continuous
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:42:02.162245+00:00
-- url     : https://prove2.me/submissions/453ace4a-2f85-4574-a526-6a79c58753dd

import Mathlib
import Definitions.Def_MasulloGRH_ZetaIntegrals
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_MasulloGRH_isRapidDecay_elemSchwartz_toFun
import Theorems.Thm_MasulloGRH_correspondence_growth_bound
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Theorems.Thm_RiemannMasullo_isCompact_closure_restrictedProduct_iff
import Theorems.Thm_MasulloGRH_tamagawa_measures_wellDefined
import Theorems.Thm_MasulloGRH_global_zeta_integral_corrected

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal RestrictedProduct

set_option autoImplicit false

universe u

namespace Sol_MasulloGRH_zetaIntegral_continuous
open MasulloGRH Topology

section Elem
variable {m n r s : ℕ} {d : Fin s → ℕ}

theorem elem_continuous (g : ElemSchwartz m n r s d) : Continuous g.toFun := by
  have hg := isRapidDecay_elemSchwartz_toFun g
  let q : (Fin m → ℝ) × (Fin n → ℝ) × ((Fin r → ℤ) × ((i : Fin s) → ZMod (d i))) →
      ElemGroup m n r s d :=
    Prod.map id (Prod.map (Pi.map fun _ => (QuotientAddGroup.mk : ℝ → UnitAddCircle)) id)
  have hq : IsOpenQuotientMap q :=
    IsOpenQuotientMap.id.prodMap
      ((IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk).prodMap
        IsOpenQuotientMap.id)
  refine hq.isQuotientMap.continuous_iff.mpr ?_
  rw [continuous_iff_continuousAt]
  rintro ⟨x0, t0, a0, b0⟩
  have hnhds : {p : (Fin m → ℝ) × (Fin n → ℝ) × ((Fin r → ℤ) × ((i : Fin s) → ZMod (d i))) |
      p.2.2 = (a0, b0)} ∈ 𝓝 (x0, t0, a0, b0) :=
    ((isOpen_discrete {(a0, b0)}).preimage (continuous_snd.comp continuous_snd)).mem_nhds rfl
  have hc : ContinuousAt (fun p : (Fin m → ℝ) × (Fin n → ℝ) × ((Fin r → ℤ) × ((i : Fin s) → ZMod (d i))) =>
      elemLift g.toFun a0 b0 (p.1, p.2.1)) (x0, t0, a0, b0) :=
    ((hg.1 a0 b0).continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).continuousAt
  refine hc.congr (Filter.mem_of_superset hnhds fun p hp => ?_)
  obtain ⟨x, t, a, b⟩ := p
  simp only [Set.mem_setOf_eq, Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  rfl

/-- The polynomial weight bound from three weighted sup bounds. -/
theorem weight_bound (h : ElemGroup m n r s d → ℂ) (N : ℕ) {ε : ℝ}
    (h0 : ∀ e, ‖h e‖ ≤ ε) (h1 : ∀ e, ‖e.1‖ ^ N * ‖h e‖ ≤ ε)
    (h2 : ∀ e, ‖e.2.2.1‖ ^ N * ‖h e‖ ≤ ε) (e : ElemGroup m n r s d) :
    ‖h e‖ * (1 + (‖e.1‖ + ‖e.2.2.1‖)) ^ N ≤ 3 ^ N * ε := by
  obtain ⟨x, z, a, b⟩ := e
  have e0 := h0 (x, z, a, b)
  have e1 := h1 (x, z, a, b)
  have e2 := h2 (x, z, a, b)
  simp only at e0 e1 e2 ⊢
  set u := ‖h (x, z, a, b)‖ with hu
  have hu0 : 0 ≤ u := norm_nonneg _
  set M := max 1 (max ‖x‖ ‖a‖) with hM
  have hM0 : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
  have hle : 1 + (‖x‖ + ‖a‖) ≤ 3 * M := by
    have := le_max_left 1 (max ‖x‖ ‖a‖)
    have := le_max_left ‖x‖ ‖a‖
    have := le_max_right ‖x‖ ‖a‖
    have := le_max_right 1 (max ‖x‖ ‖a‖)
    linarith
  have hpow : (1 + (‖x‖ + ‖a‖)) ^ N ≤ 3 ^ N * M ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hle N
  have hkey : u * M ^ N ≤ ε := by
    rcases max_choice 1 (max ‖x‖ ‖a‖) with h | h
    · rw [hM, h, one_pow, mul_one]; exact e0
    · rw [hM, h]
      rcases max_choice ‖x‖ ‖a‖ with h' | h'
      · rw [h', mul_comm]; exact e1
      · rw [h', mul_comm]; exact e2
  have hε : 0 ≤ ε := le_trans hu0 e0
  calc u * (1 + (‖x‖ + ‖a‖)) ^ N ≤ u * (3 ^ N * M ^ N) := mul_le_mul_of_nonneg_left hpow hu0
    _ = 3 ^ N * (u * M ^ N) := by ring
    _ ≤ 3 ^ N * ε := mul_le_mul_of_nonneg_left hkey (by positivity)

/-- Convergence in `S(ℝ^m × 𝕋^n × ℤ^r × F)` gives uniform convergence of the weighted values. -/
theorem eventually_weight_lt (g₀ : ElemSchwartz m n r s d) (i j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ g in 𝓝 g₀, ∀ e : ElemGroup m n r s d,
      ‖e.2.2.1‖ ^ j * ‖e.1‖ ^ i * ‖g.toFun e - g₀.toFun e‖ < ε := by
  let Ψ := fun (g : ElemSchwartz m n r s d) (p : ℕ × ℕ × ℕ) =>
      UniformFun.ofFun
        (fun q : (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
          (‖q.1‖ ^ p.2.1 * ‖q.2.2.1‖ ^ p.1) •
            iteratedFDeriv ℝ p.2.2 (elemLift g.toFun q.1 q.2.1) q.2.2)
  have hcont : Continuous Ψ := continuous_induced_dom
  have h1 : Continuous (fun g => Ψ g (i, j, 0)) := (continuous_apply _).comp hcont
  have h2 := h1.tendsto g₀
  rw [UniformFun.tendsto_iff_tendstoUniformly] at h2
  have h3 := Metric.tendstoUniformly_iff.mp h2 ε hε
  filter_upwards [h3] with g hg
  rintro ⟨x, z, a, b⟩
  choose t ht using fun j => QuotientAddGroup.mk_surjective (z j)
  have hz : z = fun j => ((t j : ℝ) : UnitAddCircle) := funext fun j => (ht j).symm
  subst hz
  have := hg (a, b, (x, t))
  simp only [Function.comp_apply] at this
  rw [dist_comm, dist_eq_norm] at this
  have key : UniformFun.toFun (Ψ g (i, j, 0)) (a, b, (x, t)) -
      UniformFun.toFun (Ψ g₀ (i, j, 0)) (a, b, (x, t)) =
      (‖a‖ ^ j * ‖x‖ ^ i) • (continuousMultilinearCurryFin0 ℝ ((Fin m → ℝ) × (Fin n → ℝ)) ℂ).symm
        (g.toFun (x, fun j => ((t j : ℝ) : UnitAddCircle), a, b) -
          g₀.toFun (x, fun j => ((t j : ℝ) : UnitAddCircle), a, b)) := by
    show (‖a‖ ^ j * ‖x‖ ^ i) • iteratedFDeriv ℝ 0 (elemLift g.toFun a b) (x, t) -
      (‖a‖ ^ j * ‖x‖ ^ i) • iteratedFDeriv ℝ 0 (elemLift g₀.toFun a b) (x, t) = _
    rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp, ← smul_sub,
      Function.comp_apply, Function.comp_apply, ← map_sub]
    rfl
  rw [key, norm_smul, LinearIsometryEquiv.norm_map, Real.norm_of_nonneg (by positivity)] at this
  exact this

/-- A Schwartz function on `ℝ^m × 𝕋^n × ℤ^r × F` which is `≥ 1` on a box. -/
theorem exists_elem_ge_one (R : ℝ) : ∃ g₀ : ElemSchwartz m n r s d,
    ∀ e : ElemGroup m n r s d, ‖e.1‖ ≤ R → ‖e.2.2.1‖ ≤ R → 1 ≤ ‖g₀.toFun e‖ := by
  classical
  set R' := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _
  let φ : ContDiffBump (0 : Fin m → ℝ) :=
    ⟨R' + 1, R' + 2, by linarith, by linarith⟩
  let ψ : (Fin m → ℝ) → ℂ := fun x => ((φ x : ℝ) : ℂ)
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ :=
    Complex.ofRealCLM.contDiff.comp φ.contDiff
  have hψc : HasCompactSupport ψ := φ.hasCompactSupport.comp_left Complex.ofReal_zero
  let G : ElemGroup m n r s d → ℂ := fun e => ψ e.1 * (if ‖e.2.2.1‖ ≤ R then 1 else 0)
  have hG : IsRapidDecay G := by
    refine ⟨fun a b => ?_, fun i j k => ?_⟩
    · show ContDiff ℝ _ (fun xt : (Fin m → ℝ) × (Fin n → ℝ) =>
        ψ xt.1 * (if ‖a‖ ≤ R then (1 : ℂ) else 0))
      exact (hψ.comp contDiff_fst).mul contDiff_const
    · have hcont : Continuous (fun x : Fin m → ℝ => ‖x‖ ^ i * ‖iteratedFDeriv ℝ k ψ x‖) :=
        (continuous_norm.pow i).mul
          (hψ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
      have hsupp : HasCompactSupport (fun x : Fin m → ℝ => ‖x‖ ^ i * ‖iteratedFDeriv ℝ k ψ x‖) :=
        ((hψc.iteratedFDeriv (𝕜 := ℝ) k).norm).mul_left
      obtain ⟨B, hB⟩ := hcont.bddAbove_range_of_hasCompactSupport hsupp
      have hB0 : 0 ≤ B := le_trans (by positivity) (hB ⟨0, rfl⟩)
      refine ⟨R' ^ j * B, fun a b xt => ?_⟩
      by_cases ha : ‖a‖ ≤ R
      · have hfun : elemLift G a b = ψ ∘ (ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ)) := by
          funext xt
          simp [elemLift, G, ha]
        rw [hfun]
        have h1 : ‖iteratedFDeriv ℝ k (ψ ∘ (ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ))) xt‖
            ≤ ‖iteratedFDeriv ℝ k ψ xt.1‖ := by
          rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ hψ xt (by exact_mod_cast le_top)]
          refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
          have h2 : ∏ _i : Fin k, ‖ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ)‖ ≤ 1 :=
            Finset.prod_le_one (fun _ _ => norm_nonneg _)
              (fun _ _ => ContinuousLinearMap.norm_fst_le _ _ _)
          calc ‖iteratedFDeriv ℝ k ψ ((ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ)) xt)‖ *
                ∏ _i : Fin k, ‖ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ)‖
              ≤ ‖iteratedFDeriv ℝ k ψ xt.1‖ * 1 :=
                mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
            _ = _ := mul_one _
        have h3 : ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k ψ xt.1‖ ≤ B := hB ⟨xt.1, rfl⟩
        have h4 : ‖a‖ ^ j ≤ R' ^ j :=
          pow_le_pow_left₀ (norm_nonneg _) (ha.trans (le_max_left _ _)) j
        calc ‖a‖ ^ j * ‖xt.1‖ ^ i *
              ‖iteratedFDeriv ℝ k (ψ ∘ (ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ))) xt‖
            ≤ R' ^ j * (‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k ψ xt.1‖) := by
              rw [mul_assoc]
              exact mul_le_mul h4 (mul_le_mul_of_nonneg_left h1 (by positivity))
                (by positivity) (by positivity)
          _ ≤ R' ^ j * B := mul_le_mul_of_nonneg_left h3 (by positivity)
      · have hfun : elemLift G a b = fun _ => 0 := by
          funext xt
          simp [elemLift, G, ha]
        rw [hfun, iteratedFDeriv_zero_fun]
        simp only [Pi.zero_apply, norm_zero, mul_zero]
        positivity
  refine ⟨⟨G, Submodule.subset_span hG⟩, fun e h1 h2 => ?_⟩
  change 1 ≤ ‖ψ e.1 * (if ‖e.2.2.1‖ ≤ R then 1 else 0)‖
  have hφ : φ e.1 = 1 := φ.one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, dist_zero_right]
    show ‖e.1‖ ≤ R' + 1
    linarith [le_max_left R 0])
  simp [ψ, hφ, h2]

end Elem
section Adele
variable {F : Type*} [Field F] [NumberField F]

instance instT2Mult : T2Space (Multiplicative (AdeleRing (𝓞 F) F)) :=
  inferInstanceAs (T2Space (AdeleRing (𝓞 F) F))

/-- The size `∑_{w ∣ ∞} ‖x_w‖` of the archimedean part of an adele. -/
noncomputable def archSize (x : AdeleRing (𝓞 F) F) : ℝ := ∑ w : InfinitePlace F, ‖x.1 w‖

theorem archSize_nonneg (x : AdeleRing (𝓞 F) F) : 0 ≤ archSize x :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem continuous_archSize : Continuous (archSize (F := F)) :=
  continuous_finsetSum _ fun w _ => ((continuous_apply w).comp continuous_fst).norm

theorem norm_natCast_completion (w : InfinitePlace F) (k : ℕ) : ‖(k : w.Completion)‖ = k := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
    map_natCast, Complex.norm_natCast]

theorem norm_two_completion (w : InfinitePlace F) : ‖(2 : w.Completion)‖ = 2 := by
  have := norm_natCast_completion w 2
  simpa using this

/-- The real coordinates `(part (ι_w x_w))_w` of the archimedean part, indexed by `Fin #S_∞`. -/
noncomputable def archCoord (part : ℂ →L[ℝ] ℝ) (x : AdeleRing (𝓞 F) F) :
    Fin (Fintype.card (InfinitePlace F)) → ℝ :=
  fun j => part (InfinitePlace.Completion.extensionEmbedding _
    (x.1 ((Fintype.equivFin (InfinitePlace F)).symm j)))

theorem continuous_archCoord (part : ℂ →L[ℝ] ℝ) :
    Continuous (archCoord (F := F) part) :=
  continuous_pi fun j => part.continuous.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding _).continuous.comp
      ((continuous_apply _).comp continuous_fst))

/-- `archCoord` as an additive map. -/
noncomputable def archCoordHom (part : ℂ →L[ℝ] ℝ) :
    AdeleRing (𝓞 F) F →+ (Fin (Fintype.card (InfinitePlace F)) → ℝ) where
  toFun := archCoord part
  map_zero' := by
    funext j
    change part (InfinitePlace.Completion.extensionEmbedding _ (0 : _)) = 0
    rw [map_zero, map_zero]
  map_add' x y := by
    funext j
    change part (InfinitePlace.Completion.extensionEmbedding _
      (x.1 ((Fintype.equivFin (InfinitePlace F)).symm j) +
        y.1 ((Fintype.equivFin (InfinitePlace F)).symm j))) = _
    rw [map_add, map_add]
    rfl

/-- `archCoord` as a continuous homomorphism to an elementary group. -/
noncomputable def archCoordElem (part : ℂ →L[ℝ] ℝ) :
    Multiplicative (AdeleRing (𝓞 F) F) →*
      Multiplicative (ElemGroup (Fintype.card (InfinitePlace F)) 0 0 0 Fin.elim0) :=
  AddMonoidHom.toMultiplicative ((archCoordHom (F := F) part).prod 0)

theorem continuous_archCoordElem (part : ℂ →L[ℝ] ℝ) :
    Continuous (archCoordElem (F := F) part) := by
  change Continuous fun x : Multiplicative (AdeleRing (𝓞 F) F) =>
    Multiplicative.ofAdd ((archCoord part (Multiplicative.toAdd x),
      (0 : (Fin 0 → UnitAddCircle) × (Fin 0 → ℤ) × ((i : Fin 0) → ZMod (Fin.elim0 i)))))
  exact continuous_ofAdd.comp (((continuous_archCoord part).comp continuous_toAdd).prodMk
    continuous_const)

theorem norm_le_archCoord (x : AdeleRing (𝓞 F) F) (j : Fin (Fintype.card (InfinitePlace F))) :
    ‖x.1 ((Fintype.equivFin (InfinitePlace F)).symm j)‖ ≤
      ‖archCoord Complex.reCLM x‖ + ‖archCoord Complex.imCLM x‖ := by
  have h1 : ‖x.1 ((Fintype.equivFin (InfinitePlace F)).symm j)‖ =
      ‖InfinitePlace.Completion.extensionEmbedding _
        (x.1 ((Fintype.equivFin (InfinitePlace F)).symm j))‖ :=
    ((InfinitePlace.Completion.isometry_extensionEmbedding _).norm_map_of_map_zero
      (map_zero _) _).symm
  have hre := norm_le_pi_norm (archCoord (F := F) Complex.reCLM x) j
  have him := norm_le_pi_norm (archCoord (F := F) Complex.imCLM x) j
  simp only [archCoord, Complex.reCLM_apply, Complex.imCLM_apply,
    Real.norm_eq_abs] at hre him
  rw [h1]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add hre him)

variable {m n r s : ℕ} {d : Fin s → ℕ}

/-- The size of `π(x)` in `ℝ^m × ℤ^r`. -/
noncomputable def elemSize (e : ElemGroup m n r s d) : ℝ := ‖e.1‖ + ‖e.2.2.1‖

theorem elemSize_nonneg (e : ElemGroup m n r s d) : 0 ≤ elemSize e := by
  unfold elemSize; positivity

/-- Linear growth: on `Γ`, the archimedean size is controlled by the size of `π`. -/
theorem growth (Γ k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F)))
    (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ p : Γ,
      1 + archSize (Multiplicative.toAdd (p : Multiplicative (AdeleRing (𝓞 F) F))) ≤
        K * (1 + elemSize (Multiplicative.toAdd (π p))) := by
  have hΓo : IsOpen (Γ : Set (Multiplicative (AdeleRing (𝓞 F) F))) := hs.1
  have hΓc : IsClosed (Γ : Set (Multiplicative (AdeleRing (𝓞 F) F))) :=
    Subgroup.isClosed_of_isOpen Γ hΓo
  have hk : IsCompact (k : Set (Multiplicative (AdeleRing (𝓞 F) F))) :=
    isCompact_of_isGoodSubgroup _ k hs.2.2.1
  have hαk : IsCompact {x : Γ | π x = 1} := by
    have : {x : Γ | π x = 1} = Subtype.val ⁻¹' (k : Set (Multiplicative (AdeleRing (𝓞 F) F))) := by
      ext x; exact hπ.2.2.2.2 x
    rw [this]
    exact hΓc.isClosedEmbedding_subtypeVal.isCompact_preimage hk
  obtain ⟨A1, B1, hAB1⟩ := correspondence_growth_bound (Multiplicative (AdeleRing (𝓞 F) F)) Γ hΓo
    m n r s d hπ.1 π hπ.2.1 hπ.2.2.1 hαk _ 0 0 0 Fin.elim0
    (archCoordElem Complex.reCLM) (continuous_archCoordElem _)
  obtain ⟨A2, B2, hAB2⟩ := correspondence_growth_bound (Multiplicative (AdeleRing (𝓞 F) F)) Γ hΓo
    m n r s d hπ.1 π hπ.2.1 hπ.2.2.1 hαk _ 0 0 0 Fin.elim0
    (archCoordElem Complex.imCLM) (continuous_archCoordElem _)
  set M : ℝ := ((Fintype.card (InfinitePlace F) : ℕ) : ℝ) with hM
  set K : ℝ := 1 + M * (|A1| + |B1| + |A2| + |B2|) with hK
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hK1 : 1 ≤ K := by
    have : 0 ≤ M * (|A1| + |B1| + |A2| + |B2|) := by positivity
    linarith
  refine ⟨K, hK1, fun p => ?_⟩
  set x := Multiplicative.toAdd (p : Multiplicative (AdeleRing (𝓞 F) F))
  set S := ‖(Multiplicative.toAdd (π p)).1‖ + ‖(Multiplicative.toAdd (π p)).2.2.1‖ with hS
  have hS0 : 0 ≤ S := by positivity
  have hre : ‖archCoord (F := F) Complex.reCLM x‖ ≤ A1 * S + B1 := by
    have := hAB1 p
    have h0 : 0 ≤ ‖(Multiplicative.toAdd (archCoordElem (F := F) Complex.reCLM
      (p : Multiplicative (AdeleRing (𝓞 F) F)))).2.2.1‖ := norm_nonneg _
    exact le_trans (le_add_of_nonneg_right h0) this
  have him : ‖archCoord (F := F) Complex.imCLM x‖ ≤ A2 * S + B2 := by
    have := hAB2 p
    have h0 : 0 ≤ ‖(Multiplicative.toAdd (archCoordElem (F := F) Complex.imCLM
      (p : Multiplicative (AdeleRing (𝓞 F) F)))).2.2.1‖ := norm_nonneg _
    exact le_trans (le_add_of_nonneg_right h0) this
  have hsize : archSize x ≤ M * ((A1 * S + B1) + (A2 * S + B2)) := by
    unfold archSize
    rw [← (Fintype.equivFin (InfinitePlace F)).symm.sum_comp]
    calc ∑ j, ‖x.1 ((Fintype.equivFin (InfinitePlace F)).symm j)‖
        ≤ ∑ _j : Fin (Fintype.card (InfinitePlace F)), ((A1 * S + B1) + (A2 * S + B2)) :=
          Finset.sum_le_sum fun j _ => (norm_le_archCoord x j).trans (add_le_add hre him)
      _ = M * ((A1 * S + B1) + (A2 * S + B2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have e1 : A1 * S ≤ |A1| * S := mul_le_mul_of_nonneg_right (le_abs_self _) hS0
  have e2 : A2 * S ≤ |A2| * S := mul_le_mul_of_nonneg_right (le_abs_self _) hS0
  have e3 : B1 ≤ |B1| := le_abs_self _
  have e4 : B2 ≤ |B2| := le_abs_self _
  have e5 : (A1 * S + B1) + (A2 * S + B2) ≤ (|A1| + |B1| + |A2| + |B2|) * (1 + S) := by
    have h6 : 0 ≤ |A1| + |A2| + |B1| * S + |B2| * S := by positivity
    have h7 : (|A1| + |B1| + |A2| + |B2|) * (1 + S) =
        (|A1| * S + |B1| + (|A2| * S + |B2|)) + (|A1| + |A2| + |B1| * S + |B2| * S) := by
      ring
    rw [h7]; linarith
  have e6 := mul_le_mul_of_nonneg_left e5 hM0
  show 1 + archSize x ≤ K * (1 + S)
  calc 1 + archSize x ≤ 1 + M * ((A1 * S + B1) + (A2 * S + B2)) := by linarith
    _ ≤ 1 + M * ((|A1| + |B1| + |A2| + |B2|) * (1 + S)) := by linarith
    _ ≤ K * (1 + S) := by
        rw [hK]
        have : 0 ≤ M * (|A1| + |B1| + |A2| + |B2|) * S := by positivity
        nlinarith

/-- The archimedean adeles `(y, 0)` lie in every open subgroup of `𝔸_F`. -/
theorem arch_mem (Γ : Subgroup (Multiplicative (AdeleRing (𝓞 F) F)))
    (hΓo : IsOpen (Γ : Set (Multiplicative (AdeleRing (𝓞 F) F)))) (y : InfiniteAdeleRing F) :
    Multiplicative.ofAdd (((y, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) :
      AdeleRing (𝓞 F) F) ∈ Γ := by
  let ι : InfiniteAdeleRing F → Multiplicative (AdeleRing (𝓞 F) F) := fun z =>
    Multiplicative.ofAdd (((z, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) :
      AdeleRing (𝓞 F) F)
  have hι : Continuous ι := continuous_ofAdd.comp (continuous_id.prodMk continuous_const)
  have hι0 : ι 0 = 1 := rfl
  let yn : ℕ → InfiniteAdeleRing F := fun k w => ((k + 1 : ℕ) : w.Completion)⁻¹ * y w
  have hyn : Filter.Tendsto yn Filter.atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun w => ?_
    show Filter.Tendsto (fun i => yn i w) Filter.atTop (𝓝 (0 : w.Completion))
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : ∀ k : ℕ, ‖yn k w‖ = ((k : ℝ) + 1)⁻¹ * ‖y w‖ := fun k => by
      simp only [yn, norm_mul, norm_inv, norm_natCast_completion]
      push_cast; ring
    simp_rw [hnorm]
    have h1 : Filter.Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.congr fun k => by simp
    simpa using h1.mul_const ‖y w‖
  have hev : ∀ᶠ k in Filter.atTop, ι (yn k) ∈ Γ := by
    have := (hι.tendsto 0).comp hyn
    rw [hι0] at this
    exact this (hΓo.mem_nhds Γ.one_mem)
  obtain ⟨k, hk⟩ := hev.exists
  have hpow : ι (yn k) ^ (k + 1) = ι y := by
    change Multiplicative.ofAdd ((k + 1) • (((yn k, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) :
      AdeleRing (𝓞 F) F)) = _
    congr 1
    refine Prod.ext ?_ ?_
    · funext w
      show (k + 1) • (((k + 1 : ℕ) : w.Completion)⁻¹ * y w) = y w
      have hne : ((k + 1 : ℕ) : w.Completion) ≠ 0 := by
        intro h
        have := norm_natCast_completion w (k + 1)
        rw [h, norm_zero] at this
        exact absurd this.symm (by positivity)
      rw [nsmul_eq_mul, ← mul_assoc, show ((k + 1 : ℕ) : w.Completion) = (k : w.Completion) + 1 by
        push_cast; ring] at *
      rw [mul_inv_cancel₀ hne, one_mul]
    · exact smul_zero _
  change ι y ∈ Γ
  rw [← hpow]
  exact Γ.pow_mem hk _

/-- The finite adeles as a restricted product. -/
abbrev FinAd (F : Type*) [Field F] [NumberField F] : Type _ :=
  Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]

theorem mem_integers_iff (v : HeightOneSpectrum (𝓞 F)) (z : v.adicCompletion F) :
    z ∈ v.adicCompletionIntegers F ↔ ‖z‖ ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).trans
    Valued.toNormedField.norm_le_one_iff.symm

/-- On `{x ∈ Γ : ∑_{w ∣ ∞} ‖x_w‖ ≤ 1}` the size of `π` is bounded: this set is compact, since
`Γ` is compactly generated, hence bounded at the finite places. -/
theorem bounded_on_unit (Γ k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F)))
    (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) :
    ∃ R : ℝ, ∀ p : Γ, archSize (Multiplicative.toAdd (p : Multiplicative (AdeleRing (𝓞 F) F))) ≤ 1 →
      elemSize (Multiplicative.toAdd (π p)) ≤ R := by
  classical
  have hΓo : IsOpen (Γ : Set (Multiplicative (AdeleRing (𝓞 F) F))) := hs.1
  have hΓc : IsClosed (Γ : Set (Multiplicative (AdeleRing (𝓞 F) F))) :=
    Subgroup.isClosed_of_isOpen Γ hΓo
  obtain ⟨U, hUc, -, -, hUgen⟩ := hs.2.1
  let pf : Multiplicative (AdeleRing (𝓞 F) F) → FinAd F :=
    fun x => (Multiplicative.toAdd x).2
  have hpf : Continuous pf := continuous_snd.comp continuous_toAdd
  have hH : IsCompact (pf '' U) := hUc.image hpf
  have hA : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      IsCompact ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) ∧
        IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    Filter.Eventually.of_forall fun v =>
      ⟨isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (v.adicCompletionIntegers F))),
        Valued.isOpen_valuationSubring _⟩
  obtain ⟨B, hBc, hBcof, hBmem⟩ :=
    (RiemannMasullo.isCompact_closure_restrictedProduct_iff hA (pf '' U)).mp
      (by rw [hH.isClosed.closure_eq]; exact hH)
  have hbd : ∀ v, ∃ C : ℝ, ∀ z ∈ B v, ‖z‖ ≤ C := fun v => (hBc v).isBounded.exists_norm_le
  choose C hC using hbd
  let Rv : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    if B v = (v.adicCompletionIntegers F : Set (v.adicCompletion F)) then 1 else max (C v) 1
  have hRv1 : ∀ v, 1 ≤ Rv v := fun v => by
    simp only [Rv]; split_ifs
    · exact le_rfl
    · exact le_max_right _ _
  have hHR : ∀ z ∈ pf '' U, ∀ v, ‖z v‖ ≤ Rv v := by
    intro z hz v
    by_cases hv : B v = (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    · have h1 := hBmem z hz v
      rw [hv] at h1
      simp only [Rv, hv, if_true]
      exact (mem_integers_iff v _).1 h1
    · simp only [Rv, hv, if_false]
      exact (hC v _ (hBmem z hz v)).trans (le_max_left _ _)
  let Γ' : Subgroup (Multiplicative (AdeleRing (𝓞 F) F)) :=
    { carrier := {x | ∀ v, ‖pf x v‖ ≤ Rv v}
      mul_mem' := fun {a b} ha hb v => by
        have : pf (a * b) v = pf a v + pf b v := rfl
        show ‖pf (a * b) v‖ ≤ Rv v
        rw [this]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha v) (hb v))
      one_mem' := fun v => by
        have : pf 1 v = 0 := rfl
        show ‖pf 1 v‖ ≤ Rv v
        rw [this, norm_zero]; exact zero_le_one.trans (hRv1 v)
      inv_mem' := fun {a} ha v => by
        have : pf a⁻¹ v = - pf a v := rfl
        show ‖pf a⁻¹ v‖ ≤ Rv v
        rw [this, norm_neg]; exact ha v }
  have hΓΓ' : Γ ≤ Γ' :=
    hUgen ▸ (Subgroup.closure_le Γ').mpr fun x hx v => hHR (pf x) ⟨x, hx, rfl⟩ v
  let W : Set (FinAd F) := {z | ∀ v, ‖z v‖ ≤ Rv v}
  have hWcl : IsClosed W := by
    have : W = ⋂ v, {z : FinAd F | ‖z v‖ ≤ Rv v} := by
      ext z; simp [W]
    rw [this]
    exact isClosed_iInter fun v =>
      isClosed_le ((RestrictedProduct.continuous_eval v).norm) continuous_const
  have hWc : IsCompact W := by
    have := (RiemannMasullo.isCompact_closure_restrictedProduct_iff hA W).mpr
      ⟨fun v => Metric.closedBall 0 (Rv v), fun v => isCompact_closedBall 0 _, ?_,
        fun z hz v => mem_closedBall_zero_iff.mpr (hz v)⟩
    · rwa [hWcl.closure_eq] at this
    · filter_upwards [hBcof] with v hv
      have : Rv v = 1 := by simp [Rv, hv]
      rw [this]; ext z; rw [mem_closedBall_zero_iff]; exact (mem_integers_iff v z).symm
  let A : Set (InfiniteAdeleRing F) := Set.pi Set.univ fun w =>
    (InfinitePlace.Completion.extensionEmbedding w) ⁻¹' Metric.closedBall 0 1
  have hAc : IsCompact A := isCompact_univ_pi fun w =>
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isClosedEmbedding.isCompact_preimage
      (isCompact_closedBall _ _)
  let KK : Set (AdeleRing (𝓞 F) F) := A ×ˢ W
  have hKK : IsCompact KK := hAc.prod hWc
  let KG : Set (Multiplicative (AdeleRing (𝓞 F) F)) := Multiplicative.ofAdd '' KK
  have hKG : IsCompact KG := hKK.image continuous_ofAdd
  have hKΓ : IsCompact (Subtype.val ⁻¹' KG : Set Γ) :=
    hΓc.isClosedEmbedding_subtypeVal.isCompact_preimage hKG
  have hφ : Continuous fun p : Γ => elemSize (Multiplicative.toAdd (π p)) := by
    unfold elemSize
    exact ((continuous_norm.comp continuous_fst).add (continuous_norm.comp
      (continuous_fst.comp (continuous_snd.comp continuous_snd)))).comp
        (continuous_toAdd.comp hπ.2.1)
  obtain ⟨R, hR⟩ := hKΓ.exists_bound_of_continuousOn hφ.continuousOn
  refine ⟨R, fun p hp => ?_⟩
  have hpK : p ∈ (Subtype.val ⁻¹' KG : Set Γ) := by
    refine ⟨Multiplicative.toAdd (p : Multiplicative (AdeleRing (𝓞 F) F)), ⟨?_, ?_⟩, rfl⟩
    · intro w _
      simp only [Set.mem_preimage, mem_closedBall_zero_iff]
      rw [(InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _)]
      refine le_trans ?_ hp
      exact Finset.single_le_sum (f := fun w =>
        ‖(Multiplicative.toAdd (p : Multiplicative (AdeleRing (𝓞 F) F))).1 w‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
    · exact hΓΓ' p.2
  have := hR p hpK
  rw [Real.norm_of_nonneg (elemSize_nonneg _)] at this
  exact this

theorem two_ne_zero_completion (w : InfinitePlace F) : (2 : w.Completion) ≠ 0 := by
  intro h
  have := norm_two_completion w
  rw [h, norm_zero] at this
  norm_num at this

/-- The idele `(2, …, 2; 1, 1, …)`. -/
noncomputable def twoIdele : IdeleGroup F where
  val := (((fun _ => 2, 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F)
  inv := (((fun _ => 2⁻¹, 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F)
  val_inv := Prod.ext (funext fun w => mul_inv_cancel₀ (two_ne_zero_completion w)) (mul_one _)
  inv_val := Prod.ext (funext fun w => inv_mul_cancel₀ (two_ne_zero_completion w)) (mul_one _)

/-- The archimedean adele `(y, 0)`. -/
noncomputable def archEmb (y : InfiniteAdeleRing F) : AdeleRing (𝓞 F) F := (y, 0)

theorem coe_twoIdele_mul (x : IdeleGroup F) :
    ((twoIdele * x : IdeleGroup F) : AdeleRing (𝓞 F) F) = (x : AdeleRing (𝓞 F) F) +
      archEmb (x : AdeleRing (𝓞 F) F).1 := by
  rw [Units.val_mul]
  refine Prod.ext ?_ ?_
  · funext w
    show (2 : w.Completion) * (x : AdeleRing (𝓞 F) F).1 w =
      (x : AdeleRing (𝓞 F) F).1 w + (x : AdeleRing (𝓞 F) F).1 w
    exact two_mul _
  · show (1 : FiniteAdeleRing (𝓞 F) F) * (x : AdeleRing (𝓞 F) F).2 =
      (x : AdeleRing (𝓞 F) F).2 + 0
    rw [one_mul, add_zero]

theorem archSize_twoIdele_mul (x : IdeleGroup F) :
    archSize ((twoIdele * x : IdeleGroup F) : AdeleRing (𝓞 F) F) =
      2 * archSize (x : AdeleRing (𝓞 F) F) := by
  unfold archSize
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [coe_twoIdele_mul]
  show ‖(x : AdeleRing (𝓞 F) F).1 w + (x : AdeleRing (𝓞 F) F).1 w‖ =
    2 * ‖(x : AdeleRing (𝓞 F) F).1 w‖
  rw [← two_mul, norm_mul, norm_two_completion]

theorem mem_twoIdele_mul (Γ : Subgroup (Multiplicative (AdeleRing (𝓞 F) F)))
    (hΓo : IsOpen (Γ : Set (Multiplicative (AdeleRing (𝓞 F) F)))) (x : IdeleGroup F) :
    Multiplicative.ofAdd ((twoIdele * x : IdeleGroup F) : AdeleRing (𝓞 F) F) ∈ Γ ↔
      Multiplicative.ofAdd (x : AdeleRing (𝓞 F) F) ∈ Γ := by
  rw [coe_twoIdele_mul, ofAdd_add]
  exact Subgroup.mul_mem_cancel_right Γ (arch_mem Γ hΓo _)

theorem ideleNorm_twoIdele : 1 < ideleNorm (twoIdele (F := F)) := by
  unfold ideleNorm
  have h1 : ∀ v, ‖((twoIdele : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ = 1 := fun v => by
    change ‖(1 : v.adicCompletion F)‖ = 1
    exact norm_one
  have h2 : ∀ w, ‖((twoIdele : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w‖ = 2 := fun w =>
    norm_two_completion w
  simp only [h1, h2, finprod_one, mul_one]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  exact one_lt_pow₀ one_lt_two (Module.finrank_pos (R := ℚ) (M := F)).ne'

theorem quasiAbscissa_eq (c : IdeleGroup F → ℂ) (σ : ℝ)
    (hσ : ∀ g : IdeleGroup F, ‖c g‖ = ideleNorm g ^ σ) : quasiAbscissa c = σ := by
  unfold quasiAbscissa
  have hex : ∃ σ' : ℝ, ∀ g : IdeleGroup F, ‖c g‖ = ideleNorm g ^ σ' := ⟨σ, hσ⟩
  rw [dif_pos hex]
  have h2 := (hex.choose_spec twoIdele).symm.trans (hσ twoIdele)
  rcases lt_trichotomy hex.choose σ with h | h | h
  · exact absurd h2 (Real.rpow_lt_rpow_of_exponent_lt ideleNorm_twoIdele h).ne
  · exact h
  · exact absurd h2 (Real.rpow_lt_rpow_of_exponent_lt ideleNorm_twoIdele h).ne'

end Adele

section Measure
variable {F : Type*} [Field F] [NumberField F]
variable {m n r s : ℕ} {d : Fin s → ℕ}

theorem eval_ofElem (Γ k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F)))
    (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) (g : ElemSchwartz m n r s d)
    (x : AdeleRing (𝓞 F) F) :
    AdelicSchwartz.eval (F := F) (SchwartzBruhat.ofElem Γ k π hs hπ g) x =
      extendPullback Γ π g.toFun (Multiplicative.ofAdd x) := rfl

theorem extendPullback_of_mem (Γ : Subgroup (Multiplicative (AdeleRing (𝓞 F) F)))
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (f : ElemGroup m n r s d → ℂ)
    {y : Multiplicative (AdeleRing (𝓞 F) F)} (h : y ∈ Γ) :
    extendPullback Γ π f y = f (Multiplicative.toAdd (π ⟨y, h⟩)) := by
  simp [extendPullback, h]

theorem extendPullback_of_notMem (Γ : Subgroup (Multiplicative (AdeleRing (𝓞 F) F)))
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (f : ElemGroup m n r s d → ℂ)
    {y : Multiplicative (AdeleRing (𝓞 F) F)} (h : y ∉ Γ) :
    extendPullback Γ π f y = 0 := by
  simp [extendPullback, h]

/-- `E_T = {x ∈ Γ : ∑_{w ∣ ∞} ‖x_w‖ < T}` as a set of ideles. -/
def truncSet (Γ : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))) (T : ℝ) : Set (IdeleGroup F) :=
  {x | Multiplicative.ofAdd (x : AdeleRing (𝓞 F) F) ∈ Γ ∧ archSize (x : AdeleRing (𝓞 F) F) < T}

/-- `Γ` as a set of ideles. -/
def ideleSet (Γ : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))) : Set (IdeleGroup F) :=
  {x | Multiplicative.ofAdd (x : AdeleRing (𝓞 F) F) ∈ Γ}

theorem isOpen_truncSet (Γ : Subgroup (Multiplicative (AdeleRing (𝓞 F) F)))
    (hΓo : IsOpen (Γ : Set (Multiplicative (AdeleRing (𝓞 F) F)))) (T : ℝ) :
    IsOpen (truncSet Γ T) :=
  (hΓo.preimage (continuous_ofAdd.comp Units.continuous_val)).inter
    (isOpen_lt (continuous_archSize.comp Units.continuous_val) continuous_const)

theorem isOpen_ideleSet (Γ : Subgroup (Multiplicative (AdeleRing (𝓞 F) F)))
    (hΓo : IsOpen (Γ : Set (Multiplicative (AdeleRing (𝓞 F) F)))) :
    IsOpen (ideleSet Γ) :=
  hΓo.preimage (continuous_ofAdd.comp Units.continuous_val)

/-- The mass of `E_T` for `|c| dμ`. -/
noncomputable def truncMass (Γ : Subgroup (Multiplicative (AdeleRing (𝓞 F) F)))
    (c : IdeleGroup F → ℂ) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (truncSet Γ T).indicator (fun x => ‖c x‖ₑ) x ∂(tamagawaIdele F)

theorem truncMass_two_mul (Γ : Subgroup (Multiplicative (AdeleRing (𝓞 F) F)))
    (hΓo : IsOpen (Γ : Set (Multiplicative (AdeleRing (𝓞 F) F))))
    (c : IdeleGroup F → ℂ) (hc : IsQuasiCharacter c) (T : ℝ) :
    truncMass Γ c (2 * T) = ‖c twoIdele‖ₑ * truncMass Γ c T := by
  haveI : (tamagawaIdele F).IsHaarMeasure := (tamagawa_measures_wellDefined F).2.1.1
  unfold truncMass
  refine (lintegral_mul_left_eq_self _ twoIdele).symm.trans ?_
  rw [← lintegral_const_mul' _ _ enorm_ne_top]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ truncSet Γ T
  · have hx' : twoIdele * x ∈ truncSet Γ (2 * T) :=
      ⟨(mem_twoIdele_mul Γ hΓo x).2 hx.1, by rw [archSize_twoIdele_mul]; linarith [hx.2]⟩
    rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx, hc.2.1, enorm_mul]
  · have hx' : twoIdele * x ∉ truncSet Γ (2 * T) := fun h => hx
      ⟨(mem_twoIdele_mul Γ hΓo x).1 h.1, by
        have := h.2; rw [archSize_twoIdele_mul] at this; linarith⟩
    rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx, mul_zero]

theorem truncMass_pow (Γ : Subgroup (Multiplicative (AdeleRing (𝓞 F) F)))
    (hΓo : IsOpen (Γ : Set (Multiplicative (AdeleRing (𝓞 F) F))))
    (c : IdeleGroup F → ℂ) (hc : IsQuasiCharacter c) (j : ℕ) :
    truncMass Γ c (2 ^ j) = ‖c twoIdele‖ₑ ^ j * truncMass Γ c 1 := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', truncMass_two_mul Γ hΓo c hc, ih, pow_succ', mul_assoc]

theorem truncMass_one_lt_top (Γ k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F)))
    (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) (c : IdeleGroup F → ℂ)
    (hint : ∀ f : AdelicSchwartz F,
      Integrable (fun g : IdeleGroup F => f.eval (g : AdeleRing (𝓞 F) F) * c g) (tamagawaIdele F)) :
    truncMass Γ c 1 < ⊤ := by
  obtain ⟨R, hR⟩ := bounded_on_unit Γ k π hs hπ
  obtain ⟨g₀, hg₀⟩ := exists_elem_ge_one (m := m) (n := n) (r := r) (s := s) (d := d) R
  let Φ : AdelicSchwartz F := SchwartzBruhat.ofElem Γ k π hs hπ g₀
  have hΦ : ∫⁻ x, ‖Φ.eval (x : AdeleRing (𝓞 F) F) * c x‖ₑ ∂(tamagawaIdele F) < ⊤ := (hint Φ).2
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hΦ
  by_cases hx : x ∈ truncSet Γ 1
  · rw [Set.indicator_of_mem hx, enorm_mul]
    have hval : Φ.eval (x : AdeleRing (𝓞 F) F) =
        g₀.toFun (Multiplicative.toAdd (π ⟨_, hx.1⟩)) := by
      rw [eval_ofElem, extendPullback_of_mem Γ π _ hx.1]
    have hb := hR ⟨_, hx.1⟩ hx.2.le
    unfold elemSize at hb
    have hge : 1 ≤ ‖Φ.eval (x : AdeleRing (𝓞 F) F)‖ := by
      rw [hval]
      exact hg₀ _ (by linarith [norm_nonneg (Multiplicative.toAdd (π ⟨_, hx.1⟩)).2.2.1])
        (by linarith [norm_nonneg (Multiplicative.toAdd (π ⟨_, hx.1⟩)).1])
    have hge' : 1 ≤ ‖Φ.eval (x : AdeleRing (𝓞 F) F)‖ₑ := by
      rw [← ofReal_norm_eq_enorm]; exact ENNReal.one_le_ofReal.mpr hge
    calc ‖c x‖ₑ = 1 * ‖c x‖ₑ := (one_mul _).symm
      _ ≤ ‖Φ.eval (x : AdeleRing (𝓞 F) F)‖ₑ * ‖c x‖ₑ := mul_le_mul_left hge' _
  · rw [Set.indicator_of_notMem hx]; exact bot_le

/-- The weighted integral `∫_Γ (1 + ∑ ‖x_w‖)^{-N} |c| dμ` is finite for `N` large. -/
theorem weighted_lt_top (Γ k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F)))
    (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) (c : IdeleGroup F → ℂ)
    (hc : IsQuasiCharacter c)
    (hint : ∀ f : AdelicSchwartz F,
      Integrable (fun g : IdeleGroup F => f.eval (g : AdeleRing (𝓞 F) F) * c g) (tamagawaIdele F)) :
    ∃ N : ℕ, ∫⁻ x, (ideleSet Γ).indicator (fun x =>
      ENNReal.ofReal ((1 + archSize (x : AdeleRing (𝓞 F) F))⁻¹ ^ N) * ‖c x‖ₑ) x
        ∂(tamagawaIdele F) < ⊤ := by
  have hΓo : IsOpen (Γ : Set (Multiplicative (AdeleRing (𝓞 F) F))) := hs.1
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖c twoIdele‖ < 2 ^ N := pow_unbounded_of_one_lt _ one_lt_two
  have hlam : ‖c twoIdele‖ₑ < 2 ^ N := by
    rw [← ofReal_norm_eq_enorm]
    have : ENNReal.ofReal ((2 : ℝ) ^ N) = 2 ^ N := by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp
    rw [← this]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hN
  refine ⟨N, ?_⟩
  set q : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ N)⁻¹ with hq
  have h2N0 : ((2 : ℝ≥0∞) ^ N) ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2Ntop : ((2 : ℝ≥0∞) ^ N) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have hqtop : q ≠ ⊤ := ENNReal.inv_ne_top.2 h2N0
  have hpt : ∀ x : IdeleGroup F, (ideleSet Γ).indicator (fun x =>
      ENNReal.ofReal ((1 + archSize (x : AdeleRing (𝓞 F) F))⁻¹ ^ N) * ‖c x‖ₑ) x ≤
      ∑' j : ℕ, 2 ^ N * q ^ j * (truncSet Γ (2 ^ j)).indicator (fun x => ‖c x‖ₑ) x := by
    intro x
    by_cases hx : x ∈ ideleSet Γ
    · rw [Set.indicator_of_mem hx]
      set θ := archSize (x : AdeleRing (𝓞 F) F) with hθ
      have hθ0 : 0 ≤ θ := archSize_nonneg _
      have hex : ∃ j : ℕ, θ < 2 ^ j := pow_unbounded_of_one_lt θ one_lt_two
      classical
      set j0 := Nat.find hex with hj0def
      have hj0 : θ < 2 ^ j0 := Nat.find_spec hex
      have hj0' : (2 : ℝ) ^ j0 ≤ 2 * (1 + θ) := by
        rcases Nat.eq_zero_or_pos j0 with h | h
        · rw [h, pow_zero]; linarith
        · have hmin := Nat.find_min hex (show j0 - 1 < j0 by omega)
          push_neg at hmin
          have : (2 : ℝ) ^ j0 = 2 * 2 ^ (j0 - 1) := by
            rw [← pow_succ']; congr 1; omega
          rw [this]; linarith
      refine le_trans ?_ (ENNReal.le_tsum j0)
      rw [Set.indicator_of_mem (show x ∈ truncSet Γ (2 ^ j0) from ⟨hx, hj0⟩)]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hreal : (1 + θ)⁻¹ ^ N ≤ (2 : ℝ) ^ N * (((2 : ℝ) ^ N)⁻¹) ^ j0 := by
        have h1 : (1 + θ)⁻¹ ≤ 2 * ((2 : ℝ) ^ j0)⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
          calc (1 + θ)⁻¹ * 2 ^ j0 ≤ (1 + θ)⁻¹ * (2 * (1 + θ)) :=
                mul_le_mul_of_nonneg_left hj0' (by positivity)
            _ = 2 := by field_simp
        calc (1 + θ)⁻¹ ^ N ≤ (2 * ((2 : ℝ) ^ j0)⁻¹) ^ N :=
              pow_le_pow_left₀ (by positivity) h1 N
          _ = (2 : ℝ) ^ N * (((2 : ℝ) ^ N)⁻¹) ^ j0 := by
              rw [mul_pow, inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm j0 N]
      calc ENNReal.ofReal ((1 + θ)⁻¹ ^ N)
          ≤ ENNReal.ofReal ((2 : ℝ) ^ N * (((2 : ℝ) ^ N)⁻¹) ^ j0) :=
            ENNReal.ofReal_le_ofReal hreal
        _ = 2 ^ N * q ^ j0 := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity) j0,
              ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num) N]
            simp [hq]
    · rw [Set.indicator_of_notMem hx]; exact bot_le
  have hmeas : ∀ j : ℕ, Measurable fun x : IdeleGroup F =>
      2 ^ N * q ^ j * (truncSet Γ (2 ^ j)).indicator (fun x => ‖c x‖ₑ) x := fun j =>
    measurable_const.mul ((hc.1.measurable.enorm).indicator
      (isOpen_truncSet Γ hΓo _).measurableSet)
  have hlt1 : ‖c twoIdele‖ₑ * q < 1 := by
    rw [hq, ← div_eq_mul_inv]
    exact (ENNReal.div_lt_iff (Or.inl h2N0) (Or.inl h2Ntop)).2 (by simpa using hlam)
  have hone := truncMass_one_lt_top Γ k π hs hπ c hint
  calc ∫⁻ x, (ideleSet Γ).indicator (fun x =>
        ENNReal.ofReal ((1 + archSize (x : AdeleRing (𝓞 F) F))⁻¹ ^ N) * ‖c x‖ₑ) x
          ∂(tamagawaIdele F)
      ≤ ∫⁻ x, ∑' j : ℕ, 2 ^ N * q ^ j * (truncSet Γ (2 ^ j)).indicator (fun x => ‖c x‖ₑ) x
          ∂(tamagawaIdele F) := lintegral_mono hpt
    _ = ∑' j : ℕ, ∫⁻ x, 2 ^ N * q ^ j * (truncSet Γ (2 ^ j)).indicator (fun x => ‖c x‖ₑ) x
          ∂(tamagawaIdele F) := lintegral_tsum fun j => (hmeas j).aemeasurable
    _ = ∑' j : ℕ, 2 ^ N * truncMass Γ c 1 * (‖c twoIdele‖ₑ * q) ^ j := by
        congr 1; funext j
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top h2Ntop (ENNReal.pow_ne_top hqtop))]
        change 2 ^ N * q ^ j * truncMass Γ c (2 ^ j) = _
        rw [truncMass_pow Γ hΓo c hc, mul_pow]
        ring
    _ = 2 ^ N * truncMass Γ c 1 * (1 - ‖c twoIdele‖ₑ * q)⁻¹ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofNat_lt_top) hone)
        (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hlt1))

end Measure

section Stage
variable {F : Type*} [Field F] [NumberField F]
variable {m n r s : ℕ} {d : Fin s → ℕ}

/-- Continuity of `g ↦ Z(ι g, c)` on a stage `S(Γ/k)` of the inductive limit. -/
theorem stage_continuous (c : IdeleGroup F → ℂ) (hc : IsQuasiCharacter c)
    (hint : ∀ f : AdelicSchwartz F,
      Integrable (fun g : IdeleGroup F => f.eval (g : AdeleRing (𝓞 F) F) * c g) (tamagawaIdele F))
    (Γ k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F)))
    (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) :
    Continuous (fun g : ElemSchwartz m n r s d =>
      zetaIntegral (SchwartzBruhat.ofElem Γ k π hs hπ g : AdelicSchwartz F) c) := by
  obtain ⟨K, hK1, hK⟩ := growth Γ k π hs hπ
  obtain ⟨N, hJ⟩ := weighted_lt_top Γ k π hs hπ c hc hint
  set J := ∫⁻ x, (ideleSet Γ).indicator (fun x =>
      ENNReal.ofReal ((1 + archSize (x : AdeleRing (𝓞 F) F))⁻¹ ^ N) * ‖c x‖ₑ) x
        ∂(tamagawaIdele F) with hJdef
  set C : ℝ := 3 ^ N * K ^ N with hC
  have hC0 : 0 ≤ C := by positivity
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro δ hδ
  have hJr : 0 ≤ J.toReal := ENNReal.toReal_nonneg
  set ε := δ / (2 * (C * J.toReal + 1)) with hεdef
  have hε : 0 < ε := by positivity
  filter_upwards [eventually_weight_lt g₀ 0 0 hε, eventually_weight_lt g₀ N 0 hε,
    eventually_weight_lt g₀ 0 N hε] with g hA hB hB'
  set h : ElemGroup m n r s d → ℂ := fun e => g.toFun e - g₀.toFun e with hh
  have h0 : ∀ e, ‖h e‖ ≤ ε := fun e => by
    have := hA e; simp only [pow_zero, one_mul] at this; exact this.le
  have h1' : ∀ e : ElemGroup m n r s d, ‖e.1‖ ^ N * ‖h e‖ ≤ ε := fun e => by
    have := hB e; simp only [pow_zero, one_mul] at this; exact this.le
  have h2' : ∀ e : ElemGroup m n r s d, ‖e.2.2.1‖ ^ N * ‖h e‖ ≤ ε := fun e => by
    have := hB' e; simp only [pow_zero, mul_one] at this; exact this.le
  have hpt : ∀ p : Γ, ‖h (Multiplicative.toAdd (π p))‖ ≤
      C * ε * (1 + archSize (Multiplicative.toAdd (p : Multiplicative (AdeleRing (𝓞 F) F))))⁻¹ ^ N := by
    intro p
    have hw := weight_bound h N h0 h1' h2' (Multiplicative.toAdd (π p))
    have hk := hK p
    set θ := archSize (Multiplicative.toAdd (p : Multiplicative (AdeleRing (𝓞 F) F)))
    set ρ := elemSize (Multiplicative.toAdd (π p)) with hρ
    have hθ0 : 0 ≤ θ := archSize_nonneg _
    have hρ0 : 0 ≤ ρ := elemSize_nonneg _
    have hpos : 0 < 1 + θ := by linarith
    have hpow : (1 + θ) ^ N ≤ K ^ N * (1 + ρ) ^ N := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hpos.le hk N
    have hkey : ‖h (Multiplicative.toAdd (π p))‖ * (1 + θ) ^ N ≤ C * ε := by
      have hw' : ‖h (Multiplicative.toAdd (π p))‖ * (1 + ρ) ^ N ≤ 3 ^ N * ε := hw
      calc ‖h (Multiplicative.toAdd (π p))‖ * (1 + θ) ^ N
          ≤ ‖h (Multiplicative.toAdd (π p))‖ * (K ^ N * (1 + ρ) ^ N) :=
            mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        _ = K ^ N * (‖h (Multiplicative.toAdd (π p))‖ * (1 + ρ) ^ N) := by ring
        _ ≤ K ^ N * (3 ^ N * ε) := mul_le_mul_of_nonneg_left hw' (by positivity)
        _ = C * ε := by rw [hC]; ring
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hpos N)]
    exact hkey
  have hdiff : zetaIntegral (SchwartzBruhat.ofElem Γ k π hs hπ g : AdelicSchwartz F) c -
      zetaIntegral (SchwartzBruhat.ofElem Γ k π hs hπ g₀ : AdelicSchwartz F) c =
      ∫ x, (AdelicSchwartz.eval (F := F) (SchwartzBruhat.ofElem Γ k π hs hπ g) (x : AdeleRing (𝓞 F) F) -
        AdelicSchwartz.eval (F := F) (SchwartzBruhat.ofElem Γ k π hs hπ g₀) (x : AdeleRing (𝓞 F) F)) *
          c x ∂(tamagawaIdele F) := by
    unfold zetaIntegral zetaIntegralFun
    rw [← integral_sub (hint _) (hint _)]
    congr 1; funext x; ring
  rw [dist_eq_norm, hdiff]
  have hle : ‖∫ x, (AdelicSchwartz.eval (F := F) (SchwartzBruhat.ofElem Γ k π hs hπ g)
        (x : AdeleRing (𝓞 F) F) -
      AdelicSchwartz.eval (F := F) (SchwartzBruhat.ofElem Γ k π hs hπ g₀) (x : AdeleRing (𝓞 F) F)) *
        c x ∂(tamagawaIdele F)‖ₑ ≤ ENNReal.ofReal (C * ε) * J := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [hJdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ ideleSet Γ
    · rw [Set.indicator_of_mem hx, eval_ofElem, eval_ofElem, extendPullback_of_mem Γ π _ hx,
        extendPullback_of_mem Γ π _ hx, enorm_mul, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity)]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hpt ⟨_, hx⟩)
    · rw [Set.indicator_of_notMem hx, mul_zero, eval_ofElem, eval_ofElem,
        extendPullback_of_notMem Γ π _ hx, extendPullback_of_notMem Γ π _ hx, sub_zero, zero_mul,
        enorm_zero]
  have hlt : ENNReal.ofReal (C * ε) * J < ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_toReal hJ.ne, ← ENNReal.ofReal_mul (by positivity)]
    refine (ENNReal.ofReal_lt_ofReal_iff hδ).2 ?_
    have hX : 0 ≤ C * J.toReal := by positivity
    have heq : C * ε * J.toReal = δ * (C * J.toReal) / (2 * (C * J.toReal + 1)) := by
      rw [hεdef]; field_simp
    rw [heq, div_lt_iff₀ (by positivity)]
    nlinarith
  have := hle.trans_lt hlt
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_lt_ofReal_iff hδ] at this
  exact this

end Stage

/-- `ℂ` with the single seminorm `‖·‖`, indexed by `PUnit`. -/
theorem norm_withSeminorms_punit :
    WithSeminorms (fun _ : PUnit.{u + 1} => normSeminorm ℂ ℂ) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf, iInf_const, coe_normSeminorm,
    comap_norm_nhds_zero]

end Sol_MasulloGRH_zetaIntegral_continuous

open MasulloGRH Sol_MasulloGRH_zetaIntegral_continuous in
theorem solution
    (F : Type*) [Field F] [NumberField F] (c : IdeleGroup F → ℂ) (hc : IsQuasiCharacter c)
    (σ : ℝ) (hσ : ∀ g : IdeleGroup F, ‖c g‖ = ideleNorm g ^ σ) (h1 : 1 < σ) :
    Continuous (fun f : AdelicSchwartz F => zetaIntegral f c) := by
  have habs : quasiAbscissa c = σ := quasiAbscissa_eq c σ hσ
  have hint : ∀ f : AdelicSchwartz F,
      Integrable (fun g : IdeleGroup F => f.eval (g : AdeleRing (𝓞 F) F) * c g)
        (tamagawaIdele F) := by
    intro f
    have h := (global_zeta_integral_corrected F f c hc).1.1 0
      (by rw [habs, Complex.zero_re, add_zero]; exact h1)
    have hq : quasiTwist c 0 = c := funext fun g => by simp [quasiTwist, normQuasiChar]
    rwa [hq] at h
  let L : AdelicSchwartz F →ₗ[ℂ] ℂ :=
    { toFun := fun f => zetaIntegral f c
      map_add' := fun f f' => by
        unfold zetaIntegral zetaIntegralFun
        rw [← integral_add (hint f) (hint f')]
        congr 1; funext x
        rw [show AdelicSchwartz.eval (F := F) (f + f') (x : AdeleRing (𝓞 F) F) =
          f.eval x + f'.eval x from rfl]
        ring
      map_smul' := fun a f => by
        unfold zetaIntegral zetaIntegralFun
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        congr 1; funext x
        rw [show AdelicSchwartz.eval (F := F) (a • f) (x : AdeleRing (𝓞 F) F) =
          a * f.eval x from rfl]
        ring }
  let t : TopologicalSpace (AdelicSchwartz F) := TopologicalSpace.induced L inferInstance
  have hLt : @Continuous _ _ t _ L := continuous_induced_dom
  refine continuous_sInf_dom (t := t) ?_ hLt
  refine ⟨⟨PUnit, inferInstance, fun _ => (normSeminorm ℂ ℂ).comp L,
    LinearMap.withSeminorms_induced norm_withSeminorms_punit L⟩, ?_⟩
  intro Γ k m n r s d π hs hπ
  exact continuous_induced_rng.2 (stage_continuous c hc hint Γ k π hs hπ)
