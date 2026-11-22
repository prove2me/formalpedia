-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_poisson_summation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:35:07.045949+00:00
-- url     : https://prove2.me/submissions/884fa040-44bc-4b32-813f-22d6f8e6987d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_LCAGroup_PlancherelMeasure
import Theorems.Thm_LCAGroup_poisson_summation
import Theorems.Thm_MasulloGRH_schwartzBruhat_cosetIntegral
import Theorems.Thm_MasulloGRH_schwartzBruhat_fourier_equiv
import Theorems.Thm_MasulloGRH_isRapidDecay_elemSchwartz_toFun

open MeasureTheory Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_schwartzBruhat_poisson_summation

open MasulloGRH

/-! ### Continuity of Schwartz–Bruhat functions -/

/-- Every element of `S(ℝ^m × 𝕋^n × ℤ^r × F)` is a continuous function. -/
theorem continuous_elem {m n r s : ℕ} {d : Fin s → ℕ} (g : ElemSchwartz m n r s d) :
    Continuous g.toFun := by
  have hg := (isRapidDecay_elemSchwartz_toFun g).1
  let q : (Fin m → ℝ) × (Fin n → ℝ) × (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) →
      ElemGroup m n r s d :=
    Prod.map id (Prod.map (Pi.map fun _ => (QuotientAddGroup.mk : ℝ → UnitAddCircle)) id)
  have hq : IsQuotientMap q :=
    (IsOpenQuotientMap.id.prodMap
      ((IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk).prodMap
        IsOpenQuotientMap.id)).isQuotientMap
  rw [hq.continuous_iff, continuous_iff_continuousAt]
  rintro ⟨x₀, t₀, a₀, b₀⟩
  have hcont : Continuous (fun p : (Fin m → ℝ) × (Fin n → ℝ) × (Fin r → ℤ) ×
      ((i : Fin s) → ZMod (d i)) => elemLift g.toFun a₀ b₀ (p.1, p.2.1)) :=
    (hg a₀ b₀).continuous.comp (by fun_prop)
  refine hcont.continuousAt.congr ?_
  have hopen : IsOpen {p : (Fin m → ℝ) × (Fin n → ℝ) × (Fin r → ℤ) ×
      ((i : Fin s) → ZMod (d i)) | p.2.2 = (a₀, b₀)} :=
    (isOpen_discrete {((a₀, b₀) : (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)))}).preimage
      (by fun_prop)
  filter_upwards [hopen.mem_nhds rfl] with p hp
  obtain ⟨x, t, a, b⟩ := p
  simp only [Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  rfl

/-- The extension by zero of the pull-back of a continuous function along a continuous
homomorphism defined on an open subgroup is continuous. -/
theorem continuous_extendPullback {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] {m n r s : ℕ} {d : Fin s → ℕ} (Γ : Subgroup G)
    (hΓ : IsOpen (Γ : Set G)) (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hπ : Continuous π) (g : ElemGroup m n r s d → ℂ) (hg : Continuous g) :
    Continuous (extendPullback Γ π g) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Γ
  · have hon : ContinuousOn (extendPullback Γ π g) (Γ : Set G) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : Set.domRestrict (Γ : Set G) (extendPullback Γ π g) =
          fun y : (Γ : Set G) => g (Multiplicative.toAdd (π ⟨y.1, y.2⟩)) := by
        funext y
        show extendPullback Γ π g y.1 = _
        exact dif_pos y.2
      rw [this]
      exact hg.comp (continuous_toAdd.comp (hπ.comp (by fun_prop)))
    exact hon.continuousAt (hΓ.mem_nhds hx)
  · have hcl : IsClosed (Γ : Set G) := Subgroup.isClosed_of_isOpen Γ hΓ
    have h0 : extendPullback Γ π g =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
      simp only [extendPullback, dif_neg (show y ∉ Γ from hy)]
    exact continuousAt_const.congr h0.symm

/-- Every Schwartz–Bruhat function is continuous. -/
theorem continuous_sb {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    (f : SchwartzBruhat G) : Continuous (f : G → ℂ) := by
  obtain ⟨f, hf⟩ := f
  show Continuous f
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hx
    exact continuous_extendPullback Γ hs.1 π hπ.2.1 _ (continuous_elem g)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

end Sol_MasulloGRH_schwartzBruhat_poisson_summation

open MasulloGRH Sol_MasulloGRH_schwartzBruhat_poisson_summation in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
    [MeasurableSpace (PontryaginDual (G ⧸ H))] [BorelSpace (PontryaginDual (G ⧸ H))]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]
    (ν : Measure (G ⧸ H)) [ν.IsHaarMeasure] [ν.Regular]
    (hν : ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x, φ x ∂μ = ∫ q : G ⧸ H, (∫ h : H, φ (q.out * (h : G)) ∂μH) ∂ν)
    (ν' : Measure (PontryaginDual (G ⧸ H))) (hν' : LCAGroup.IsPlancherelMeasure ν ν')
    (f : SchwartzBruhat G) (y : G) :
    Integrable (fun η : PontryaginDual (G ⧸ H) =>
        (∫ x : G, f x * star (η (x : G ⧸ H) : ℂ) ∂μ) * (η (y : G ⧸ H) : ℂ)) ν' ∧
    ∫ h : H, f (y * (h : G)) ∂μH =
      ∫ η : PontryaginDual (G ⧸ H),
        (∫ x : G, f x * star (η (x : G ⧸ H) : ℂ) ∂μ) * (η (y : G ⧸ H) : ℂ) ∂ν' := by
  have : IsClosed (H : Set G) := hH
  have : ν'.IsHaarMeasure := hν'.1
  have : ν'.Regular := hν'.2.1
  -- The coset-integration map `Φ_H : S(G) → S(G/H)`.
  obtain ⟨Φ, -, hΦ⟩ := schwartzBruhat_cosetIntegral G H hH μH
  -- Schwartz–Bruhat functions are integrable, and the Fourier transform maps `S` into `S`.
  obtain ⟨_, hFG⟩ := schwartzBruhat_fourier_equiv G μ
  obtain ⟨F, hF⟩ := schwartzBruhat_fourier_equiv (G ⧸ H) ν
  obtain ⟨_, hF'⟩ := schwartzBruhat_fourier_equiv (PontryaginDual (G ⧸ H)) ν'
  have hf : Integrable (f : G → ℂ) μ := (hFG f).1
  -- The function `q ↦ ∫_H f (q.out h) dμH` is `Φ_H f`.
  have hΦq : (fun q : G ⧸ H => ∫ h : H, f (q.out * (h : G)) ∂μH) = (Φ f : G ⧸ H → ℂ) := by
    funext q
    have h := (hΦ f q.out).2
    rw [QuotientGroup.out_eq'] at h
    exact h.symm
  obtain ⟨h1, h2⟩ := LCAGroup.poisson_summation G H hH μ μH ν hν ν' hν' (f : G → ℂ) hf
  -- The restriction of `f̂` to `(G/H)^` is the Fourier transform of `Φ_H f`, a Schwartz–Bruhat
  -- function on the dual group; hence it is integrable.
  have hfun : (fun η : PontryaginDual (G ⧸ H) => ∫ x : G, f x * star (η (x : G ⧸ H) : ℂ) ∂μ) =
      (F (Φ f) : PontryaginDual (G ⧸ H) → ℂ) := by
    funext η
    rw [(hF (Φ f)).2 η, ← h1 η, hΦq]
  have hint : Integrable
      (fun η : PontryaginDual (G ⧸ H) => ∫ x : G, f x * star (η (x : G ⧸ H) : ℂ) ∂μ) ν' := by
    rw [hfun]
    exact (hF' (F (Φ f))).1
  refine ⟨?_, ?_⟩
  · have h0 : Continuous fun η : PontryaginDual (G ⧸ H) =>
        (η : ContinuousMonoidHom (G ⧸ H) Circle).toContinuousMap :=
      (ContinuousMonoidHom.isInducing_toContinuousMap (G ⧸ H) Circle).continuous
    have h1' : Continuous fun g : C(G ⧸ H, Circle) => g (y : G ⧸ H) :=
      continuous_eval_const _
    have h2' : Continuous fun η : PontryaginDual (G ⧸ H) => η (y : G ⧸ H) := h1'.comp h0
    have hc : Continuous fun η : PontryaginDual (G ⧸ H) => (η (y : G ⧸ H) : ℂ) :=
      continuous_subtype_val.comp h2'
    exact hint.mul_bdd (c := 1) hc.aestronglyMeasurable
      (.of_forall fun η ↦ by rw [Circle.norm_coe])
  · -- The coset integral is continuous on `G`, as the pull-back of `Φ_H f ∈ S(G/H)`.
    have hfib : ∀ y : G, Integrable (fun h : H => f (y * (h : G))) μH := fun y => (hΦ f y).1
    have hcomp : (fun y : G => ∫ h : H, f (y * (h : G)) ∂μH) =
        (Φ f : G ⧸ H → ℂ) ∘ (QuotientGroup.mk : G → G ⧸ H) := by
      funext y
      exact ((hΦ f y).2).symm
    have hcont : Continuous (fun y : G => ∫ h : H, f (y * (h : G)) ∂μH) := by
      rw [hcomp]
      exact (continuous_sb (Φ f)).comp QuotientGroup.continuous_mk
    exact (h2 hint).2 hfib hcont y
