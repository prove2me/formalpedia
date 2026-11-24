-- Prove2me | solution 1 for GlobalTheory.ThetaRational.isIntegral_and_rational
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:08:26.803867+00:00
-- url     : https://prove2.me/submissions/fc53c2a3-6020-42f7-acc4-13c2692b6ba9

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta
import Theorems.Thm_GlobalTheory_ThetaRational_eq_zero_of_mul_eq_zero
import Theorems.Thm_P2M_GlobalTheory_ThetaRational_algHom_eval__435c3be33efa
import Theorems.Thm_GlobalTheory_ThetaRational_algHom_apply_mv
import Theorems.Thm_GlobalTheory_ThetaRational_exists_algHom
import Theorems.Thm_GlobalTheory_ThetaRational_growth_finite
import Theorems.Thm_GlobalTheory_ThetaRational_growth_root
import Theorems.Thm_GlobalTheory_ThetaRational_analyticAt_eval
import Theorems.Thm_GlobalTheory_ThetaRational_differentiable_of_mem_adjoin
import Theorems.Thm_GlobalTheory_ThetaRational_exists_eval_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [Fintype ι]
namespace GlobalTheory.ThetaRational
theorem _root_.solution
    (hnoeth : (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a))
    (hrat : (∀ (d m : ℕ) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ) (φ : (Fin d → ℂ) × ℂ → ℂ) (C : ℝ), p.Monic → q ≠ 0 → Polynomial.C q ∈ Ideal.span {p, p.derivative} → (∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, ∃ F : (Fin d → ℂ) × ℂ → ℂ, AnalyticAt ℂ F z ∧ ∀ᶠ w in 𝓝[{z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}] z, φ w = F w) → (∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, ‖φ z‖ ≤ C * (1 + ‖z.1‖) ^ m) → (∃ s : Polynomial (MvPolynomial (Fin d) ℂ), s.Monic ∧ ∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, (s.map (MvPolynomial.eval z.1)).eval (φ z) = 0) ∧ ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), ∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, (p.derivative.map (MvPolynomial.eval z.1)).eval z.2 * φ z = (r.map (MvPolynomial.eval z.1)).eval z.2))
    {u : ι → E → ℂ} {h : E → ℂ} (hu : ∀ c, Differentiable ℂ (u c)) (hh : Differentiable ℂ h)
    (hcl : ∀ y : ι → ℂ, (∀ F : MvPolynomial ι ℂ, (∀ e, MvPolynomial.eval (fun c => u c e) F = 0) →
      MvPolynomial.eval y F = 0) → ∃ e, y = fun c => u c e)
    {c₀ : ι} (hc₀ : u c₀ ≠ 0)
    (hdesc : ∀ e, (fun c => u c e) ≠ 0 → ∃ G : (ι → ℂ) → ℂ, AnalyticAt ℂ G (fun c => u c e) ∧
      ∀ᶠ y in 𝓝 (fun c => u c e), ∀ x, (fun c => u c x) = y → h x = G y)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C) (hgr : ∀ e, ‖h e‖ ≤ C * ‖fun c => u c e‖ ^ m) :
    IsIntegral (Algebra.adjoin ℂ (Set.range u)) h ∧
      ∃ a ∈ Algebra.adjoin ℂ (Set.range u), ∃ b ∈ Algebra.adjoin ℂ (Set.range u),
        b ≠ 0 ∧ b * h = a := by
  set A := Algebra.adjoin ℂ (Set.range u) with hA
  have hd : ∀ b : A, Differentiable ℂ b.1 := fun b => differentiable_of_mem_adjoin hu b.2
  have : NoZeroDivisors A := ⟨fun {b b'} hb => by
    by_cases h0 : b = 0
    · exact Or.inl h0
    refine Or.inr (Subtype.ext (eq_zero_of_mul_eq_zero (hd b).continuous (hd b')
      (fun h1 => h0 (Subtype.ext h1)) fun e he => ?_))
    exact (mul_eq_zero.1 (congrFun (congrArg Subtype.val hb) e)).resolve_left he⟩
  have : IsDomain A := NoZeroDivisors.to_isDomain A
  have : Algebra.FiniteType ℂ A := .adjoin_of_finite (Set.finite_range u)
  obtain ⟨n, j, a, p, q₀, -, hj, hfin, hpm, -, hp, hq₀, hq₀p, hq₀b⟩ := hnoeth A
  set g : ι → A := fun c => ⟨u c, Algebra.subset_adjoin ⟨c, rfl⟩⟩ with hg
  have hint : ∀ b : A, j.toRingHom.IsIntegralElem b := hfin.to_isIntegral

  obtain ⟨q₁, hq₁, b₁, hb₁⟩ : ∃ q₁ : MvPolynomial (Fin n) ℂ, q₁ ≠ 0 ∧ ∃ b₁, j q₁ = b₁ * g c₀ := by
    letI := j.toRingHom.toAlgebra
    have h1 := Ideal.comap_ne_bot_of_integral_mem (R := MvPolynomial (Fin n) ℂ) (x := g c₀)
      (I := Ideal.span {g c₀}) (fun h => hc₀ (congrArg Subtype.val h))
      (Ideal.mem_span_singleton_self _) (hint _)
    obtain ⟨q₁, h2, h3⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h1
    obtain ⟨b₁, h4⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 h2)
    exact ⟨q₁, h3, b₁, h4.symm⟩
  obtain ⟨q, hqdef⟩ : ∃ q, q = q₁ * q₀ := ⟨_, rfl⟩
  have hq : q ≠ 0 := hqdef ▸ mul_ne_zero hq₁ hq₀
  have hqp : Polynomial.C q ∈ Ideal.span {p, p.derivative} := by
    rw [hqdef, map_mul]
    exact Ideal.mul_mem_left _ _ hq₀p
  have hqb : ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin n) ℂ),
      j q * b = r.eval₂ j.toRingHom a := by
    intro b
    obtain ⟨r, hr⟩ := hq₀b (j q₁ * b)
    exact ⟨r, by rw [← hr, hqdef, map_mul]; ring⟩
  let ev : E → A →ₐ[ℂ] ℂ := fun e => (Pi.evalAlgHom ℂ (fun _ : E => ℂ) e).comp A.val
  have hev : ∀ e (b : A), ev e b = b.1 e := fun _ _ => rfl
  let x : E → Fin n → ℂ := fun e i => ev e (j (MvPolynomial.X i))
  let pr : E → (Fin n → ℂ) × ℂ := fun e => (x e, ev e a)
  have hx : ∀ e s, ev e (j s) = MvPolynomial.eval (x e) s := fun e s => algHom_apply_mv j (ev e) s
  have hpr : ∀ e (r : Polynomial (MvPolynomial (Fin n) ℂ)) (b : A), ev e (r.eval₂ j.toRingHom b) =
      (r.map (MvPolynomial.eval (x e))).eval (ev e b) := fun e r b => algHom_eval₂ j (ev e) r b
  set Z : Set ((Fin n → ℂ) × ℂ) := {z : (Fin n → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧
    (p.map (MvPolynomial.eval z.1)).eval z.2 = 0} with hZ
  have hprZ : ∀ e, MvPolynomial.eval (x e) q ≠ 0 → pr e ∈ Z := fun e he =>
    ⟨he, by rw [← hpr, (hp p).2 dvd_rfl, map_zero]⟩
  have hsurj : ∀ w ∈ Z, ∃ e, pr e = w := by
    intro w hw
    obtain ⟨χ, h1, h2⟩ := exists_algHom j a p q (fun r => (hp r).1) hqb w hw.1 hw.2
    obtain ⟨e, he⟩ := exists_eval_eq hcl χ
    exact ⟨e, Prod.ext (funext fun i => (he _).symm.trans (h1 i)) ((he _).symm.trans h2)⟩
  choose R hR using fun c => hqb (g c)
  let ρ : (Fin n → ℂ) × ℂ → ι → ℂ := fun w c =>
    ((R c).map (MvPolynomial.eval w.1)).eval w.2 / MvPolynomial.eval w.1 q
  have hρ : ∀ e, MvPolynomial.eval (x e) q ≠ 0 → (fun c => u c e) = ρ (pr e) := by
    intro e he
    funext c
    change _ = ((R c).map (MvPolynomial.eval (x e))).eval (ev e a) / MvPolynomial.eval (x e) q
    rw [eq_div_iff he, ← hpr, ← hR, map_mul, hx, mul_comm]
    rfl
  have hne : ∀ e, MvPolynomial.eval (x e) q ≠ 0 → (fun c => u c e) ≠ 0 := by
    intro e he h0
    apply he
    have : ev e (g c₀) = 0 := congrFun h0 c₀
    rw [hqdef, map_mul, ← hx e q₁, hb₁, map_mul, this, mul_zero, zero_mul]
  classical
  let φ : (Fin n → ℂ) × ℂ → ℂ := fun w => h (Function.invFun pr w)
  have hinv : ∀ w ∈ Z, pr (Function.invFun pr w) = w := fun w hw => Function.invFun_eq (hsurj w hw)
  have hinv' : ∀ w ∈ Z, MvPolynomial.eval (x (Function.invFun pr w)) q ≠ 0 := by
    intro w hw
    have : x (Function.invFun pr w) = w.1 := congrArg Prod.fst (hinv w hw)
    rw [this]
    exact hw.1
  have hφ : ∀ e, MvPolynomial.eval (x e) q ≠ 0 → φ (pr e) = h e := by
    intro e he
    obtain ⟨G, -, hG⟩ := hdesc e (hne e he)
    have hG' := hG.self_of_nhds
    rw [hG' e rfl]
    refine hG' _ ?_
    rw [hρ _ (hinv' _ (hprZ e he)), hinv _ (hprZ e he), hρ e he]
  obtain ⟨C', m', hC', hgr'⟩ := growth_finite (fun e => 1 + ‖x e‖) (fun e => by simp) u fun c => by
    obtain ⟨s, hs, hs'⟩ := hint (g c)
    obtain ⟨C', m', hC', h1⟩ := growth_root s hs
    exact ⟨C', m', hC', fun e => h1 (x e) (ev e (g c)) (by rw [← hpr, hs', map_zero])⟩
  obtain ⟨⟨s, hs, hs'⟩, r, hr⟩ := hrat n (m' * m) p q φ (C * C' ^ m) hpm hq hqp
    (fun w hw => by
      obtain ⟨e, rfl⟩ := hsurj w hw
      obtain ⟨G, hGa, hG⟩ := hdesc e (hne e hw.1)
      rw [hρ e hw.1] at hGa hG
      have hρa : AnalyticAt ℂ ρ (pr e) := by
        refine analyticAt_pi_iff.2 fun c => (analyticAt_eval (R c) _).fun_div ?_ hw.1
        simpa using analyticAt_eval (Polynomial.C q) (pr e)
      refine ⟨G ∘ ρ, hGa.comp hρa, ?_⟩
      filter_upwards [nhdsWithin_le_nhds (hρa.continuousAt.eventually hG), self_mem_nhdsWithin]
        with w h1 h2
      refine h1 _ ?_
      rw [hρ _ (hinv' _ h2), hinv _ h2])
    (fun w hw => by
      obtain ⟨e, rfl⟩ := hsurj w hw
      rw [hφ e hw.1]
      refine (hgr e).trans ?_
      have h1 : ‖fun c => u c e‖ ≤ C' * (1 + ‖x e‖) ^ m' :=
        (pi_norm_le_iff_of_nonneg (by positivity)).2 (hgr' e)
      rw [mul_assoc, pow_mul, ← mul_pow]
      gcongr)
  have hjq : j q ≠ 0 := fun h0 => hq (hj (h0.trans (map_zero j).symm))
  constructor
  · refine ⟨s.map j.toRingHom, hs.map _, ?_⟩
    have h1 : ∀ e, Polynomial.eval₂ (algebraMap A (E → ℂ)) h (s.map j.toRingHom) e =
        (s.map (MvPolynomial.eval (x e))).eval (h e) := by
      intro e
      have := Polynomial.hom_eval₂ (s.map j.toRingHom) (algebraMap A (E → ℂ))
        (Pi.evalRingHom (fun _ : E => ℂ) e) h
      refine this.trans ?_
      rw [Polynomial.eval₂_map, Polynomial.eval_map]
      congr 1
      exact RingHom.ext fun s => hx e s
    refine eq_zero_of_mul_eq_zero (hd (j q)).continuous ?_ (fun h0 => hjq (Subtype.ext h0))
      fun e he => ?_
    · rw [funext h1]
      intro e
      have h2 : Differentiable ℂ (fun e => (x e, h e)) :=
        (differentiable_pi.2 fun i => hd _).prodMk hh
      exact (analyticAt_eval s (x e, h e)).differentiableAt.comp e (h2 e)
    · rw [← hev, hx] at he
      rw [h1, ← hφ e he]
      exact hs' _ (hprZ e he)
  · refine ⟨(j q * r.eval₂ j.toRingHom a).1, Subtype.prop _,
      (j q * p.derivative.eval₂ j.toRingHom a).1, Subtype.prop _, fun h0 => ?_, funext fun e => ?_⟩
    · have h1 : p.derivative.eval₂ j.toRingHom a = 0 :=
        (mul_eq_zero.1 (Subtype.ext h0 : j q * _ = 0)).resolve_left hjq
      obtain ⟨α, β, h2⟩ := Ideal.mem_span_pair.1 hqp
      have h3 := congrArg (Polynomial.eval₂ j.toRingHom a) h2
      rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, h1,
        (hp p).2 dvd_rfl, Polynomial.eval₂_C] at h3
      exact hjq (by simpa using h3.symm)
    · rw [Pi.mul_apply, ← hev, ← hev, map_mul, map_mul, hx, hpr, hpr, mul_assoc]
      by_cases he : MvPolynomial.eval (x e) q = 0
      · rw [he, zero_mul, zero_mul]
      · rw [← hφ e he]
        congr 1
        exact hr _ (hprZ e he)
end GlobalTheory.ThetaRational
