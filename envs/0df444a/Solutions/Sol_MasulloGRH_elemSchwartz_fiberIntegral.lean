-- Prove2me | solution 1 for MasulloGRH.elemSchwartz_fiberIntegral
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T20:14:56.239397+00:00
-- url     : https://prove2.me/submissions/70eef7bf-f351-490c-b7f9-1d4504e5b7a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Theorems.Thm_MasulloGRH_elemSchwartz_fiberIntegral_continuous
import Theorems.Thm_MasulloGRH_isRapidDecay_elemSchwartz_toFun

open MeasureTheory Topology

set_option autoImplicit false

/-!
Reduction of `MasulloGRH.elemSchwartz_fiberIntegral` to
`MasulloGRH.elemSchwartz_fiberIntegral_continuous` (fibre integration is a continuous linear map
`S(E) → S(E')` satisfying the coset-integral formula).  The surjectivity is proved here by a
normalised cut-off, following the proof of `elementary_fiberIntegral_lift` in the open
formalization mccorvie/riemann-masullo (Apache-2.0).
-/

namespace Sol_MasulloGRH_elemSchwartz_fiberIntegral

open MasulloGRH
open scoped ContDiff

theorem gaussian_weight_bound (b : ℝ) (hb : 0 < b) (m : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → (1 + t) ^ m * Real.exp (-b * t ^ 2) ≤ C := by
  let D := (m.factorial : ℝ) / b ^ m
  refine ⟨2 ^ m * max 1 D, fun t ht => ?_⟩
  have he : Real.exp (-b * t ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le) (sq_nonneg _))
  by_cases h : t ≤ 1
  · calc
      _ ≤ (2 : ℝ) ^ m * 1 := by gcongr; linarith
      _ ≤ _ := by gcongr; exact le_max_left ..
  · have ht' : 1 ≤ t := le_of_not_ge h
    have hpol : t ^ (2 * m) * Real.exp (-b * t ^ 2) ≤ D := by
      have hy := Real.pow_div_factorial_le_exp _ (mul_nonneg hb.le (sq_nonneg t)) m
      rw [mul_pow, ← pow_mul] at hy
      rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      dsimp [D]
      rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hb m)]
      simpa only [mul_comm] using (div_le_iff₀ (by positivity : (0 : ℝ) < m.factorial)).mp hy
    calc
      _ ≤ (2 * t ^ 2) ^ m * Real.exp (-b * t ^ 2) := by gcongr; nlinarith [sq_nonneg (t - 1)]
      _ = 2 ^ m * (t ^ (2 * m) * Real.exp (-b * t ^ 2)) := by rw [mul_pow, pow_mul, mul_assoc]
      _ ≤ _ := by gcongr; exact hpol.trans (le_max_right ..)

/-- A Gaussian on a real inner product space is a Schwartz function (ported from the open
formalization mccorvie/riemann-masullo). -/
theorem exists_gaussian_schwartz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ∃ g : SchwartzMap E ℂ, ∀ x, g x = (Real.exp (-‖x‖ ^ 2) : ℂ) := by
  let b : ℝ := 1
  have hb : (0 : ℝ) < b := one_pos
  let p (x : E) := -b * ‖x‖ ^ 2
  have hp : p.HasTemperateGrowth := by
    have h := (Function.hasTemperateGrowth_norm_sq E).neg
    have : p = -(fun x : E => ‖x‖ ^ 2) := by funext x; simp [p, b]
    rw [this]; exact h
  let G : SchwartzMap E ℝ :=
    { toFun := Real.exp ∘ p
      smooth' := Real.contDiff_exp.comp hp.1
      decay' := by
        intro k n
        obtain ⟨j, C, hC, hj⟩ := hp.norm_iteratedFDeriv_le_uniform n
        obtain ⟨M, hM⟩ := gaussian_weight_bound b hb (k + j * n)
        refine ⟨n.factorial * (C + 1) ^ n * M, fun x => ?_⟩
        let X := 1 + ‖x‖
        have hX : 1 ≤ X := by simp [X]
        have hD : 1 ≤ (C + 1) * X ^ j :=
          one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hX)
        have H := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (n := n) (N := ∞) Real.contDiff_exp hp.1
          (mod_cast le_top) x (C := Real.exp (p x)) (D := (C + 1) * X ^ j) (fun i _ => by
            rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
              Real.iter_deriv_exp, Real.norm_of_nonneg (Real.exp_pos _).le]) (fun i hi hin =>
            (hj i hin x).trans
            ((by gcongr; linarith : C * X ^ j ≤ (C + 1) * X ^ j).trans (le_self_pow₀ hD (by omega))))
        calc
          _ ≤ X ^ k * (n.factorial * Real.exp (p x) * ((C + 1) * X ^ j) ^ n) := by
              gcongr; simp [X]
          _ = (n.factorial * (C + 1) ^ n) * (X ^ (k + j * n) * Real.exp (p x)) := by
              rw [mul_pow, pow_add, pow_mul]; ring
          _ ≤ _ := by gcongr; exact hM ‖x‖ (norm_nonneg x) }
  exact ⟨SchwartzMap.postcompCLM Complex.ofRealCLM G, fun x => by
    change ((Real.exp (p x) : ℝ) : ℂ) = _
    simp only [p, b, neg_mul, one_mul]⟩

/-- A positive Schwartz function on `ℝ^N` (with the sup norm). -/
theorem exists_pos_schwartz (N : ℕ) :
    ∃ g : SchwartzMap (Fin N → ℝ) ℂ, ∀ x, ∃ t : ℝ, 0 < t ∧ g x = (t : ℂ) := by
  obtain ⟨g, hg⟩ := exists_gaussian_schwartz (E := EuclideanSpace ℝ (Fin N))
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv (Fin N) ℝ).symm g,
    fun x => ⟨Real.exp (-‖(EuclideanSpace.equiv (Fin N) ℝ).symm x‖ ^ 2), Real.exp_pos _, ?_⟩⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hg]

theorem norm_intCast_pi {r : ℕ} (a : Fin r → ℤ) : ‖(fun i => (a i : ℝ))‖ = ‖a‖ := by
  have h : ‖(fun i => (a i : ℝ))‖₊ = ‖a‖₊ := by
    rw [Pi.nnnorm_def, Pi.nnnorm_def]
    congr 1
  exact congrArg NNReal.toReal h

/-- A positive Schwartz–Bruhat function on `ℝ^m × 𝕋^n × ℤ^r × F`. -/
theorem exists_pos_elemSchwartz (m n r s : ℕ) (d : Fin s → ℕ) :
    ∃ θ : ElemSchwartz m n r s d, ∀ e, ∃ t : ℝ, 0 < t ∧ θ.toFun e = (t : ℂ) := by
  obtain ⟨G, hG⟩ := exists_pos_schwartz m
  obtain ⟨H, hH⟩ := exists_pos_schwartz r
  let f : ElemGroup m n r s d → ℂ := fun e => H (fun i => (e.2.2.1 i : ℝ)) * G e.1
  have hGs : ContDiff ℝ ∞ (G ∘ Prod.fst : (Fin m → ℝ) × (Fin n → ℝ) → ℂ) :=
    (G.smooth ⊤).comp contDiff_fst
  have hl : ∀ a b, elemLift f a b = fun xt => H (fun i => (a i : ℝ)) • (G ∘ Prod.fst) xt := by
    intro a b; funext xt; rfl
  have hf : IsRapidDecay f := by
    refine ⟨fun a b => ?_, fun i j k => ?_⟩
    · rw [hl]; exact hGs.const_smul _
    · obtain ⟨CH, hCH⟩ := H.decay j 0
      obtain ⟨CG, hCG⟩ := G.decay i k
      refine ⟨CH * CG, fun a b xt => ?_⟩
      rw [hl, iteratedFDeriv_const_smul_apply' (hGs.contDiffAt.of_le (by exact_mod_cast le_top)),
        show (⇑G ∘ Prod.fst : (Fin m → ℝ) × (Fin n → ℝ) → ℂ) =
          ⇑G ∘ ⇑(ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ)) from rfl,
        (ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ)).iteratedFDeriv_comp_right
          (G.smooth ⊤) xt (by exact_mod_cast le_top)]
      have h1 : ‖(iteratedFDeriv ℝ k (⇑G) xt.1).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ))‖ ≤
          ‖iteratedFDeriv ℝ k (⇑G) xt.1‖ := by
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        refine mul_le_of_le_one_right (norm_nonneg _) ?_
        exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
          (fun _ _ => ContinuousLinearMap.norm_fst_le _ _ _)
      have h2 := hCH.2 (fun i => (a i : ℝ))
      rw [norm_iteratedFDeriv_zero, norm_intCast_pi] at h2
      have h3 := hCG.2 xt.1
      rw [norm_smul]
      calc ‖a‖ ^ j * ‖xt.1‖ ^ i * (‖H (fun i => (a i : ℝ))‖ *
            ‖(iteratedFDeriv ℝ k (⇑G) xt.1).compContinuousLinearMap
              (fun _ => ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ))‖)
          ≤ ‖a‖ ^ j * ‖xt.1‖ ^ i * (‖H (fun i => (a i : ℝ))‖ * ‖iteratedFDeriv ℝ k (⇑G) xt.1‖) := by
            gcongr
        _ = (‖a‖ ^ j * ‖H (fun i => (a i : ℝ))‖) * (‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (⇑G) xt.1‖) := by
            ring
        _ ≤ CH * CG := mul_le_mul h2 h3 (by positivity) ((by positivity : (0:ℝ) ≤ _).trans h2)
  refine ⟨⟨f, Submodule.subset_span hf⟩, fun e => ?_⟩
  obtain ⟨t₁, ht₁, he₁⟩ := hH (fun i => (e.2.2.1 i : ℝ))
  obtain ⟨t₂, ht₂, he₂⟩ := hG e.1
  refine ⟨t₁ * t₂, mul_pos ht₁ ht₂, ?_⟩
  change H (fun i => (e.2.2.1 i : ℝ)) * G e.1 = _
  rw [he₁, he₂, Complex.ofReal_mul]

theorem coe_intCast_unitAddCircle (k : ℤ) : (((k : ℝ)) : UnitAddCircle) = 0 := by
  have h : ((k : ℝ)) = k • (1 : ℝ) := by simp
  rw [h, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]

/-- On the compact elementary group `𝕋^n × F` every function that is smooth in the torus
variables is a Schwartz–Bruhat function. -/
theorem isRapidDecay_of_compact {n s : ℕ} {d : Fin s → ℕ} (hd : ∀ i, d i ≠ 0)
    (F : ElemGroup 0 n 0 s d → ℂ) (hF : ∀ a b, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (elemLift F a b)) :
    IsRapidDecay F := by
  classical
  have : ∀ i, NeZero (d i) := fun i => ⟨hd i⟩
  refine ⟨hF, fun i j k => ?_⟩
  have hb : ∀ b : (i : Fin s) → ZMod (d i), ∃ C : ℝ, ∀ xt,
      ‖iteratedFDeriv ℝ k (elemLift F 0 b) xt‖ ≤ C := by
    intro b
    have hφc : Continuous (fun xt => iteratedFDeriv ℝ k (elemLift F 0 b) xt) :=
      (hF 0 b).continuous_iteratedFDeriv (by exact_mod_cast le_top)
    let K : Set ((Fin 0 → ℝ) × (Fin n → ℝ)) :=
      {0} ×ˢ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)
    have hK : IsCompact K := isCompact_singleton.prod (isCompact_univ_pi fun _ => isCompact_Icc)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hφc.continuousOn
    refine ⟨C, fun xt => ?_⟩
    let v : (Fin 0 → ℝ) × (Fin n → ℝ) := (0, fun j => -(⌊xt.2 j⌋ : ℝ))
    have hper : (fun z => elemLift F 0 b (z + v)) = elemLift F 0 b := by
      funext z
      unfold elemLift
      congr 1
      refine Prod.ext (Subsingleton.elim _ _) (Prod.ext ?_ rfl)
      funext j
      change (((z.2 j + -(⌊xt.2 j⌋ : ℝ) : ℝ)) : UnitAddCircle) = ((z.2 j : ℝ) : UnitAddCircle)
      rw [AddCircle.coe_add, show (-(⌊xt.2 j⌋ : ℝ)) = ((-⌊xt.2 j⌋ : ℤ) : ℝ) by push_cast; ring,
        coe_intCast_unitAddCircle, add_zero]
    have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := elemLift F 0 b) k v xt
    rw [hper] at h
    rw [h]
    refine hC _ ⟨Set.mem_singleton_iff.mpr (Subsingleton.elim _ _), fun j _ => ?_⟩
    change 0 ≤ xt.2 j + -(⌊xt.2 j⌋ : ℝ) ∧ xt.2 j + -(⌊xt.2 j⌋ : ℝ) ≤ 1
    constructor
    · linarith [Int.floor_le (xt.2 j)]
    · linarith [Int.lt_floor_add_one (xt.2 j)]
  choose C hC using hb
  refine ⟨∑ b, |C b|, fun a b xt => ?_⟩
  have ha : a = 0 := Subsingleton.elim _ _
  subst ha
  have hx : ‖xt.1‖ = 0 := by rw [Subsingleton.elim xt.1 0, norm_zero]
  have h0 : ‖(0 : Fin 0 → ℤ)‖ = 0 := norm_zero
  rw [hx, h0]
  calc (0 : ℝ) ^ j * 0 ^ i * ‖iteratedFDeriv ℝ k (elemLift F 0 b) xt‖
      ≤ 1 * 1 * ‖iteratedFDeriv ℝ k (elemLift F 0 b) xt‖ := by
        gcongr
        · exact pow_le_one₀ le_rfl zero_le_one
        · exact pow_le_one₀ le_rfl zero_le_one
    _ ≤ C b := by rw [one_mul, one_mul]; exact hC b xt
    _ ≤ |C b| := le_abs_self _
    _ ≤ ∑ b, |C b| := Finset.single_le_sum (f := fun b => |C b|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ b)

section maps

variable {m n r s : ℕ} {d : Fin s → ℕ} {m' n' r' s' : ℕ} {d' : Fin s' → ℕ}

/-- The vector part `x ↦ π(L(x, 0))` of the section. -/
def vecSec (L : (Fin m' → ℝ) × (Fin n' → ℝ) →L[ℝ] (Fin m → ℝ) × (Fin n → ℝ)) :
    (Fin m' → ℝ) →+ ElemGroup m n r s d where
  toFun x := ((L (x, 0)).1, fun j => (((L (x, 0)).2 j : ℝ) : UnitAddCircle), 0, 0)
  map_zero' := by
    have h : L ((0 : Fin m' → ℝ), (0 : Fin n' → ℝ)) = 0 := by
      rw [Prod.mk_zero_zero, map_zero]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · simp [h]
    · funext j; simp [h]
  map_add' x y := by
    have h : L (x + y, (0 : Fin n' → ℝ)) = L (x, 0) + L (y, 0) := by
      rw [← map_add, Prod.mk_add_mk, add_zero]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext (add_zero 0).symm (add_zero 0).symm))
    · simp [h]
    · funext j; simp [h, AddCircle.coe_add]

theorem continuous_vecSec (L : (Fin m' → ℝ) × (Fin n' → ℝ) →L[ℝ] (Fin m → ℝ) × (Fin n → ℝ)) :
    Continuous (vecSec (r := r) (s := s) (d := d) L) := by
  have h : Continuous (fun x : Fin m' → ℝ => L (x, 0)) :=
    L.continuous.comp (continuous_id.prodMk continuous_const)
  exact h.fst.prodMk ((continuous_pi fun j =>
    (continuous_quotient_mk'.comp ((continuous_apply j).comp h.snd))).prodMk continuous_const)

/-- The lattice part `a ↦ ∑ aᵢ wᵢ` of the section. -/
def latSec (w : Fin r' → ElemGroup m n r s d) : (Fin r' → ℤ) →+ ElemGroup m n r s d where
  toFun a := ∑ i, a i • w i
  map_zero' := by simp
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]

/-- The section `E' → E` of `p` on the noncompact factors `ℝ^{m'} × ℤ^{r'}`. -/
def secA (L : (Fin m' → ℝ) × (Fin n' → ℝ) →L[ℝ] (Fin m → ℝ) × (Fin n → ℝ))
    (w : Fin r' → ElemGroup m n r s d) : ElemGroup m' n' r' s' d' →+ ElemGroup m n r s d :=
  (vecSec L).comp (AddMonoidHom.fst _ _) +
    (latSec w).comp ((AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp (AddMonoidHom.snd _ _)))

theorem secA_apply (L : (Fin m' → ℝ) × (Fin n' → ℝ) →L[ℝ] (Fin m → ℝ) × (Fin n → ℝ))
    (w : Fin r' → ElemGroup m n r s d) (x : ElemGroup m' n' r' s' d') :
    secA L w x = vecSec L x.1 + latSec w x.2.2.1 := rfl

theorem continuous_secA (L : (Fin m' → ℝ) × (Fin n' → ℝ) →L[ℝ] (Fin m → ℝ) × (Fin n → ℝ))
    (w : Fin r' → ElemGroup m n r s d) : Continuous (secA (s' := s') (d' := d') L w) :=
  ((continuous_vecSec L).comp continuous_fst).add
    ((continuous_of_discreteTopology (f := latSec w)).comp continuous_snd.snd.fst)

/-- The projection `E' → 𝕋^{n'} × F'` onto the compact factors. -/
def cA : ElemGroup m' n' r' s' d' →+ ElemGroup 0 n' 0 s' d' where
  toFun w := (0, w.2.1, 0, w.2.2.2)
  map_zero' := rfl
  map_add' _ _ := Prod.ext (add_zero 0).symm (Prod.ext rfl (Prod.ext (add_zero 0).symm rfl))

theorem continuous_cA : Continuous (cA (m' := m') (n' := n') (r' := r') (s' := s') (d' := d')) :=
  continuous_const.prodMk (continuous_snd.fst.prodMk (continuous_const.prodMk continuous_snd.snd.snd))

/-- The inclusion of the compact factors. -/
def jf (u : ElemGroup 0 n' 0 s' d') : ElemGroup m' n' r' s' d' := (0, u.2.1, 0, u.2.2.2)

end maps

/-- A continuous homomorphism `ℝ → ℝ/ℤ` is `t ↦ t w mod ℤ`. -/
theorem exists_lift (c : ℝ →+ UnitAddCircle) (hc : Continuous c) :
    ∃ w : ℝ, ∀ t : ℝ, ((t * w : ℝ) : UnitAddCircle) = c t := by
  let q : ℝ → UnitAddCircle := (↑)
  have hq : IsCoveringMap q := AddCircle.isCoveringMap_coe (1 : ℝ)
  obtain ⟨L, ⟨hL0, hL⟩, _⟩ := hq.existsUnique_continuousMap_lifts
    (⟨c, hc⟩ : C(ℝ, UnitAddCircle)) 0 0 (by simp [q])
  have hLift (t : ℝ) : q (L t) = c t := congrFun hL t
  have hAdd (s t : ℝ) : L (s + t) = L s + L t := by
    have hAgree : q ∘ (fun p : ℝ × ℝ ↦ L (p.1 + p.2)) =
        q ∘ (fun p : ℝ × ℝ ↦ L p.1 + L p.2) := by
      funext p
      change q (L (p.1 + p.2)) = ((L p.1 + L p.2 : ℝ) : UnitAddCircle)
      rw [AddCircle.coe_add]
      change q (L (p.1 + p.2)) = q (L p.1) + q (L p.2)
      simp only [hLift, map_add]
    exact congrFun (hq.eq_of_comp_eq (L.continuous.comp (continuous_fst.add continuous_snd))
      ((L.continuous.comp continuous_fst).add (L.continuous.comp continuous_snd))
      hAgree (0, 0) (by simp [hL0])) (s, t)
  let L' : ℝ →+ ℝ := { toFun := L, map_zero' := hL0, map_add' := hAdd }
  refine ⟨L 1, fun t => ?_⟩
  have hLinear : L t = t * L 1 := by
    have h := map_real_smul L' L.continuous t (1 : ℝ)
    simp only [smul_eq_mul, mul_one] at h
    exact h
  rw [← hLinear]
  exact hLift t

section lin

variable {m n r s : ℕ} {d : Fin s → ℕ} {m' n' r' s' : ℕ} {d' : Fin s' → ℕ}

/-- Structure of a continuous one-parameter subgroup of `ℝ^m × 𝕋^n × ℤ^r × F`. -/
theorem flow_structure (ψ : ℝ →+ ElemGroup m n r s d) (hψ : Continuous ψ) :
    ∃ u : (Fin m → ℝ) × (Fin n → ℝ), ∀ t : ℝ,
      (ψ t).1 = t • u.1 ∧ (∀ j, (ψ t).2.1 j = ((t * u.2 j : ℝ) : UnitAddCircle)) ∧
        (ψ t).2.2 = 0 := by
  have h1 : ∀ t : ℝ, (ψ t).1 = t • (ψ 1).1 := by
    intro t
    have := map_real_smul ((AddMonoidHom.fst _ _).comp ψ) (continuous_fst.comp hψ) t (1 : ℝ)
    simpa using this
  have h2 : ∀ j : Fin n, ∃ w : ℝ, ∀ t : ℝ, ((t * w : ℝ) : UnitAddCircle) = (ψ t).2.1 j :=
    fun j => exists_lift ((Pi.evalAddMonoidHom _ j).comp
      ((AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp ψ)))
      ((continuous_apply j).comp (continuous_fst.comp (continuous_snd.comp hψ)))
  choose w hw using h2
  have h3 : ∀ t : ℝ, (ψ t).2.2 = 0 := by
    intro t
    have := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℝ)
      (continuous_snd.comp (continuous_snd.comp hψ)) (x := t) (y := 0)
    simpa using this
  exact ⟨((ψ 1).1, w), fun t => ⟨h1 t, fun j => (hw j t).symm, h3 t⟩⟩

/-- The covering map `ℝ^m × ℝ^n → ℝ^m × 𝕋^n ⊆ E`. -/
def cov : (Fin m → ℝ) × (Fin n → ℝ) →+ ElemGroup m n r s d where
  toFun v := (v.1, fun j => ((v.2 j : ℝ) : UnitAddCircle), 0, 0)
  map_zero' := by
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    funext j; simp
  map_add' u v := by
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext (add_zero 0).symm (add_zero 0).symm))
    funext j; simp

theorem cov_apply (v : (Fin m → ℝ) × (Fin n → ℝ)) :
    (cov (r := r) (s := s) (d := d) v) = (v.1, fun j => ((v.2 j : ℝ) : UnitAddCircle), 0, 0) := rfl

theorem continuous_cov : Continuous (cov (m := m) (n := n) (r := r) (s := s) (d := d)) := by
  have h : Continuous (fun v : (Fin m → ℝ) × (Fin n → ℝ) => v) := continuous_id
  exact h.fst.prodMk ((continuous_pi fun j =>
    continuous_quotient_mk'.comp ((continuous_apply j).comp h.snd)).prodMk continuous_const)

/-- The restriction of an open continuous homomorphism of elementary groups to the vector
covers lifts to a surjective linear map, which has a linear section. -/
theorem linearSection
    (p : Multiplicative (ElemGroup m n r s d) →* Multiplicative (ElemGroup m' n' r' s' d'))
    (hpc : Continuous p) (hpo : IsOpenMap p) :
    ∃ L : (Fin m' → ℝ) × (Fin n' → ℝ) →L[ℝ] (Fin m → ℝ) × (Fin n → ℝ),
      ∀ v : (Fin m' → ℝ) × (Fin n' → ℝ),
        p (Multiplicative.ofAdd
            ((L v).1, fun j => (((L v).2 j : ℝ) : UnitAddCircle), 0, 0)) =
          Multiplicative.ofAdd (v.1, fun j => ((v.2 j : ℝ) : UnitAddCircle), 0, 0) := by
  classical
  let pA : ElemGroup m n r s d →+ ElemGroup m' n' r' s' d' := AddMonoidHom.toMultiplicative.symm p
  have hpAc : Continuous pA := hpc
  have hpAo : IsOpenMap pA := hpo
  let φ : (Fin m → ℝ) × (Fin n → ℝ) →+ ElemGroup m' n' r' s' d' := pA.comp cov
  have hφc : Continuous φ := hpAc.comp continuous_cov
  have hflow : ∀ v : (Fin m → ℝ) × (Fin n → ℝ), ∃ u : (Fin m' → ℝ) × (Fin n' → ℝ),
      ∀ t : ℝ, φ (t • v) = cov (t • u) := by
    intro v
    let ψ : ℝ →+ ElemGroup m' n' r' s' d' :=
      { toFun := fun t => φ (t • v), map_zero' := by simp,
        map_add' := fun a c => by simp [add_smul] }
    have hψ : Continuous ψ := hφc.comp (continuous_id.smul continuous_const)
    obtain ⟨u, hu⟩ := flow_structure ψ hψ
    refine ⟨u, fun t => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hu t
    refine Prod.ext h1 (Prod.ext (funext fun j => (h2 j).trans ?_) h3)
    simp [cov_apply]
  choose U hU using hflow
  let b := Module.finBasis ℝ ((Fin m → ℝ) × (Fin n → ℝ))
  let Λ : ((Fin m → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ((Fin m' → ℝ) × (Fin n' → ℝ)) :=
    b.constr ℝ (fun i => U (b i))
  have hΛ : ∀ v, φ v = cov (Λ v) := by
    intro v
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    simp only [hU]
    rw [← map_sum]
    congr 1
    simp [Λ]
  have hmem : ∀ v' : (Fin m' → ℝ) × (Fin n' → ℝ), ∃ v, φ v = cov v' := by
    let H : AddSubgroup (ElemGroup m' n' r' s' d') := φ.range
    have hrange : Set.range (cov (m := m) (n := n) (r := r) (s := s) (d := d)) =
        {e : ElemGroup m n r s d | e.2.2 = 0} := by
      ext e
      constructor
      · rintro ⟨v, rfl⟩; rfl
      · intro he
        have hz : ∀ j, ∃ z : ℝ, (z : UnitAddCircle) = e.2.1 j := fun j =>
          QuotientAddGroup.mk_surjective (e.2.1 j)
        choose z hz using hz
        exact ⟨(e.1, z), Prod.ext rfl (Prod.ext (funext hz) he.symm)⟩
    have hopen0 : IsOpen {e : ElemGroup m n r s d | e.2.2 = 0} :=
      (isOpen_discrete ({0} : Set ((Fin r → ℤ) × ((i : Fin s) → ZMod (d i))))).preimage
        continuous_snd.snd
    have hHopen : IsOpen (H : Set (ElemGroup m' n' r' s' d')) := by
      have : (H : Set (ElemGroup m' n' r' s' d')) = pA '' {e | e.2.2 = 0} := by
        rw [← hrange, ← Set.range_comp]
        rfl
      rw [this]; exact hpAo _ hopen0
    have hHclosed : IsClosed (H : Set (ElemGroup m' n' r' s' d')) :=
      AddSubgroup.isClosed_of_isOpen H hHopen
    have hconn : IsPreconnected (Set.range (cov (m := m') (n := n') (r := r') (s := s') (d := d'))) :=
      isPreconnected_range continuous_cov
    have hsub : Set.range (cov (m := m') (n := n') (r := r') (s := s') (d := d')) ⊆ H :=
      hconn.subset_isClopen ⟨hHclosed, hHopen⟩ ⟨0, ⟨0, map_zero _⟩, H.zero_mem⟩
    intro v'
    obtain ⟨v, hv⟩ := hsub ⟨v', rfl⟩
    exact ⟨v, hv⟩
  have hsurj : LinearMap.range Λ = ⊤ := by
    let W := LinearMap.range Λ
    have hWc : IsClosed (W : Set ((Fin m' → ℝ) × (Fin n' → ℝ))) := W.closed_of_finiteDimensional
    let f : (Fin n' → ℤ) → Set ((Fin m' → ℝ) × (Fin n' → ℝ)) := fun k =>
      (Homeomorph.addRight (((0 : Fin m' → ℝ), fun j => (k j : ℝ)))) '' (W : Set _)
    have hcover : ⋃ k, f k = Set.univ := by
      refine Set.eq_univ_of_forall fun v' => ?_
      obtain ⟨v, hv⟩ := hmem v'
      rw [hΛ] at hv
      have h1 : (Λ v).1 = v'.1 := by
        have := congrArg Prod.fst hv
        exact this
      have h2 : ∀ j, ∃ k : ℤ, v'.2 j = (Λ v).2 j + k := by
        intro j
        have h := congrFun (congrArg (fun e : ElemGroup m' n' r' s' d' => e.2.1) hv) j
        have h' : (((v'.2 j - (Λ v).2 j : ℝ)) : UnitAddCircle) = 0 := by
          rw [AddCircle.coe_sub]
          change (((Λ v).2 j : ℝ) : UnitAddCircle) = ((v'.2 j : ℝ) : UnitAddCircle) at h
          rw [h, sub_self]
        obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h'
        refine ⟨k, ?_⟩
        rw [zsmul_eq_mul, mul_one] at hk
        linarith
      choose k hk using h2
      refine Set.mem_iUnion.mpr ⟨k, Λ v, ⟨v, rfl⟩, ?_⟩
      change Λ v + (((0 : Fin m' → ℝ), fun j => (k j : ℝ))) = v'
      refine Prod.ext ?_ ?_
      · simp [h1]
      · funext j; simp [hk j]
    have hfc : ∀ k, IsClosed (f k) := fun k => (Homeomorph.addRight _).isClosedMap _ hWc
    obtain ⟨k, hk⟩ := nonempty_interior_of_iUnion_of_closed hfc hcover
    have hint : (interior (W : Set ((Fin m' → ℝ) × (Fin n' → ℝ)))).Nonempty := by
      rw [← Homeomorph.image_interior] at hk
      exact Set.image_nonempty.mp hk
    exact Submodule.eq_top_of_nonempty_interior' W hint
  obtain ⟨R, hR⟩ := Λ.exists_rightInverse_of_surjective hsurj
  refine ⟨LinearMap.toContinuousLinearMap R, fun v => ?_⟩
  have h := hΛ (R v)
  rw [show Λ (R v) = v from LinearMap.congr_fun hR v] at h
  exact congrArg Multiplicative.ofAdd h

end lin

section pull

variable {m n r s : ℕ} {d : Fin s → ℕ} {m₁ n₁ r₁ s₁ : ℕ} {d₁ : Fin s₁ → ℕ}
  {m₂ n₂ r₂ s₂ : ℕ} {d₂ : Fin s₂ → ℕ}

/-- A continuous homomorphism out of the vector cover lifts to a linear map. -/
theorem exists_linear_lift (φ : (Fin m → ℝ) × (Fin n → ℝ) →+ ElemGroup m₁ n₁ r₁ s₁ d₁)
    (hφc : Continuous φ) :
    ∃ Λ : (Fin m → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin m₁ → ℝ) × (Fin n₁ → ℝ),
      ∀ v, φ v = cov (Λ v) := by
  classical
  have hflow : ∀ v : (Fin m → ℝ) × (Fin n → ℝ), ∃ u : (Fin m₁ → ℝ) × (Fin n₁ → ℝ),
      ∀ t : ℝ, φ (t • v) = cov (t • u) := by
    intro v
    let ψ : ℝ →+ ElemGroup m₁ n₁ r₁ s₁ d₁ :=
      { toFun := fun t => φ (t • v), map_zero' := by simp,
        map_add' := fun a c => by simp [add_smul] }
    have hψ : Continuous ψ := hφc.comp (continuous_id.smul continuous_const)
    obtain ⟨u, hu⟩ := flow_structure ψ hψ
    refine ⟨u, fun t => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hu t
    refine Prod.ext h1 (Prod.ext (funext fun j => (h2 j).trans ?_) h3)
    simp [cov_apply]
  choose U hU using hflow
  let b := Module.finBasis ℝ ((Fin m → ℝ) × (Fin n → ℝ))
  let Λ : ((Fin m → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ((Fin m₁ → ℝ) × (Fin n₁ → ℝ)) :=
    b.constr ℝ (fun i => U (b i))
  refine ⟨LinearMap.toContinuousLinearMap Λ, fun v => ?_⟩
  change φ v = cov (Λ v)
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum]
  simp only [hU]
  rw [← map_sum]
  congr 1
  simp [Λ]

/-- Pull-back of an elementary function along a continuous homomorphism, on one fibre. -/
theorem pull_affine (φA : ElemGroup m n r s d →+ ElemGroup m₁ n₁ r₁ s₁ d₁) (hφ : Continuous φA) :
    ∃ Λ : (Fin m → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin m₁ → ℝ) × (Fin n₁ → ℝ), ∀ a b,
      ∃ (c : (Fin m₁ → ℝ) × (Fin n₁ → ℝ)) (a₁ : Fin r₁ → ℤ) (b₁ : (i : Fin s₁) → ZMod (d₁ i)),
        ∀ v, φA (v.1, fun j => ((v.2 j : ℝ) : UnitAddCircle), a, b) =
          ((Λ v + c).1, fun j => (((Λ v + c).2 j : ℝ) : UnitAddCircle), a₁, b₁) := by
  obtain ⟨Λ, hΛ⟩ := exists_linear_lift (φA.comp cov) (hφ.comp continuous_cov)
  have hΛ' : ∀ v, φA (cov v) = cov (Λ v) := hΛ
  refine ⟨Λ, fun a b => ?_⟩
  have hz : ∀ j, ∃ t : ℝ, (t : UnitAddCircle) = (φA (0, 0, a, b)).2.1 j := fun j =>
    QuotientAddGroup.mk_surjective _
  choose t₀ ht₀ using hz
  refine ⟨((φA (0, 0, a, b)).1, t₀), (φA (0, 0, a, b)).2.2.1, (φA (0, 0, a, b)).2.2.2, fun v => ?_⟩
  have hsplit : ((v.1, fun j => ((v.2 j : ℝ) : UnitAddCircle), a, b) : ElemGroup m n r s d) =
      cov v + (0, 0, a, b) := by
    refine Prod.ext (add_zero _).symm (Prod.ext ?_ (Prod.ext (zero_add _).symm (zero_add _).symm))
    funext j; simp [cov_apply]
  rw [hsplit, map_add, hΛ' v]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp [cov_apply]
  · funext j; simp [cov_apply, ht₀ j]
  · simp [cov_apply]
  · simp [cov_apply]

theorem deriv_affine_bound (G : (Fin m₁ → ℝ) × (Fin n₁ → ℝ) → ℂ) (hG : ContDiff ℝ ∞ G)
    (Λ : (Fin m → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin m₁ → ℝ) × (Fin n₁ → ℝ)) (c) (l : ℕ) (v) :
    ‖iteratedFDeriv ℝ l (fun v => G (Λ v + c)) v‖ ≤ ‖Λ‖ ^ l * ‖iteratedFDeriv ℝ l G (Λ v + c)‖ := by
  have h1 : (fun v => G (Λ v + c)) = (fun w => G (w + c)) ∘ Λ := rfl
  have hGc : ContDiff ℝ ∞ (fun w => G (w + c)) := hG.comp (contDiff_id.add contDiff_const)
  rw [h1, Λ.iteratedFDeriv_comp_right hGc v (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [iteratedFDeriv_comp_add_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]

theorem pow3 {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (N : ℕ) :
    (1 + (X + Y)) ^ N ≤ 3 ^ N * (1 + X ^ N + Y ^ N) := by
  set M := max 1 (max X Y)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hXM : X ≤ M := (le_max_left X Y).trans (le_max_right _ _)
  have hYM : Y ≤ M := (le_max_right X Y).trans (le_max_right _ _)
  have h1 : 1 + (X + Y) ≤ 3 * M := by linarith
  have h2 : M ^ N ≤ 1 + X ^ N + Y ^ N := by
    rcases max_choice 1 (max X Y) with h | h
    · rw [show M = 1 from h, one_pow]; have := pow_nonneg hX N; have := pow_nonneg hY N; linarith
    · rcases max_choice X Y with h' | h'
      · rw [show M = X from h.trans h']; have := pow_nonneg hY N; linarith
      · rw [show M = Y from h.trans h']; have := pow_nonneg hX N; linarith
  calc (1 + (X + Y)) ^ N ≤ (3 * M) ^ N := pow_le_pow_left₀ (by positivity) h1 N
    _ = 3 ^ N * M ^ N := mul_pow _ _ _
    _ ≤ _ := by gcongr

theorem weight_bound (g : ElemGroup m₁ n₁ r₁ s₁ d₁ → ℂ) (hg : IsRapidDecay g) (N l : ℕ) :
    ∃ M : ℝ, ∀ a b xt, (1 + (‖xt.1‖ + ‖a‖)) ^ N *
      ‖iteratedFDeriv ℝ l (elemLift g a b) xt‖ ≤ M := by
  obtain ⟨C₀, h₀⟩ := hg.2 0 0 l
  obtain ⟨C₁, h₁⟩ := hg.2 N 0 l
  obtain ⟨C₂, h₂⟩ := hg.2 0 N l
  refine ⟨3 ^ N * (C₀ + C₁ + C₂), fun a b xt => ?_⟩
  have e0 := h₀ a b xt
  have e1 := h₁ a b xt
  have e2 := h₂ a b xt
  simp only [pow_zero, one_mul, mul_one] at e0 e1 e2
  have key := pow3 (norm_nonneg xt.1) (norm_nonneg a) N
  set D := ‖iteratedFDeriv ℝ l (elemLift g a b) xt‖
  have hD : 0 ≤ D := norm_nonneg _
  calc (1 + (‖xt.1‖ + ‖a‖)) ^ N * D ≤ 3 ^ N * (1 + ‖xt.1‖ ^ N + ‖a‖ ^ N) * D :=
        mul_le_mul_of_nonneg_right key hD
    _ = 3 ^ N * (D + ‖xt.1‖ ^ N * D + ‖a‖ ^ N * D) := by ring
    _ ≤ 3 ^ N * (C₀ + C₁ + C₂) := by gcongr

theorem isRapidDecay_mul_pull
    (φA : ElemGroup m n r s d →+ ElemGroup m₁ n₁ r₁ s₁ d₁)
    (ψA : ElemGroup m n r s d →+ ElemGroup m₂ n₂ r₂ s₂ d₂)
    (hφ : Continuous φA) (hψ : Continuous ψA) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ z : ElemGroup m n r s d, ‖z.1‖ + ‖z.2.2.1‖ ≤
      K * ((1 + (‖(φA z).1‖ + ‖(φA z).2.2.1‖)) * (1 + (‖(ψA z).1‖ + ‖(ψA z).2.2.1‖))))
    (g₁ : ElemGroup m₁ n₁ r₁ s₁ d₁ → ℂ) (g₂ : ElemGroup m₂ n₂ r₂ s₂ d₂ → ℂ)
    (h₁ : IsRapidDecay g₁) (h₂ : IsRapidDecay g₂) :
    IsRapidDecay (fun z => g₁ (φA z) * g₂ (ψA z)) := by
  obtain ⟨Λ₁, hΛ₁⟩ := pull_affine φA hφ
  obtain ⟨Λ₂, hΛ₂⟩ := pull_affine ψA hψ
  have hrep : ∀ a b, ∃ (c₁ : (Fin m₁ → ℝ) × (Fin n₁ → ℝ)) (a₁ : Fin r₁ → ℤ)
      (b₁ : (i : Fin s₁) → ZMod (d₁ i)) (c₂ : (Fin m₂ → ℝ) × (Fin n₂ → ℝ)) (a₂ : Fin r₂ → ℤ)
      (b₂ : (i : Fin s₂) → ZMod (d₂ i)),
      elemLift (fun z => g₁ (φA z) * g₂ (ψA z)) a b =
        (fun v => elemLift g₁ a₁ b₁ (Λ₁ v + c₁) * elemLift g₂ a₂ b₂ (Λ₂ v + c₂)) ∧
      ∀ v : (Fin m → ℝ) × (Fin n → ℝ), ‖v.1‖ + ‖a‖ ≤
        K * ((1 + (‖(Λ₁ v + c₁).1‖ + ‖a₁‖)) * (1 + (‖(Λ₂ v + c₂).1‖ + ‖a₂‖))) := by
    intro a b
    obtain ⟨c₁, a₁, b₁, hc₁⟩ := hΛ₁ a b
    obtain ⟨c₂, a₂, b₂, hc₂⟩ := hΛ₂ a b
    refine ⟨c₁, a₁, b₁, c₂, a₂, b₂, ?_, fun v => ?_⟩
    · funext v
      change g₁ (φA (v.1, fun j => ((v.2 j : ℝ) : UnitAddCircle), a, b)) *
        g₂ (ψA (v.1, fun j => ((v.2 j : ℝ) : UnitAddCircle), a, b)) = _
      rw [hc₁ v, hc₂ v]; rfl
    · have h := hb (v.1, fun j => ((v.2 j : ℝ) : UnitAddCircle), a, b)
      rw [hc₁ v, hc₂ v] at h
      exact h
  refine ⟨fun a b => ?_, fun i j k => ?_⟩
  · obtain ⟨c₁, a₁, b₁, c₂, a₂, b₂, hF, -⟩ := hrep a b
    rw [hF]
    exact ((h₁.1 a₁ b₁).comp (Λ₁.contDiff.add contDiff_const)).mul
      ((h₂.1 a₂ b₂).comp (Λ₂.contDiff.add contDiff_const))
  · choose M₁ hM₁ using fun l => weight_bound g₁ h₁ (i + j) l
    choose M₂ hM₂ using fun l => weight_bound g₂ h₂ (i + j) l
    refine ⟨K ^ (i + j) * ∑ l ∈ Finset.range (k + 1),
      (k.choose l : ℝ) * (‖Λ₁‖ ^ l * M₁ l) * (‖Λ₂‖ ^ (k - l) * M₂ (k - l)), fun a b v => ?_⟩
    obtain ⟨c₁, a₁, b₁, c₂, a₂, b₂, hF, hw⟩ := hrep a b
    rw [hF]
    set N := i + j with hN
    set A₁ := 1 + (‖(Λ₁ v + c₁).1‖ + ‖a₁‖) with hA₁def
    set A₂ := 1 + (‖(Λ₂ v + c₂).1‖ + ‖a₂‖) with hA₂def
    have hA₁ : 0 ≤ A₁ := by positivity
    have hA₂ : 0 ≤ A₂ := by positivity
    set S := ‖v.1‖ + ‖a‖ with hSdef
    have hS0 : 0 ≤ S := by positivity
    have hS : ‖a‖ ^ j * ‖v.1‖ ^ i ≤ S ^ N := by
      calc ‖a‖ ^ j * ‖v.1‖ ^ i ≤ S ^ j * S ^ i :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left (norm_nonneg _)) j)
              (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_right (norm_nonneg _)) i)
              (by positivity) (by positivity)
        _ = S ^ N := by rw [← pow_add, add_comm]
    have hSK : S ^ N ≤ K ^ N * (A₁ ^ N * A₂ ^ N) := by
      rw [← mul_pow, ← mul_pow]
      exact pow_le_pow_left₀ hS0 (hw v) N
    have hG₁ : ContDiff ℝ ∞ (fun v => elemLift g₁ a₁ b₁ (Λ₁ v + c₁)) :=
      (h₁.1 a₁ b₁).comp (Λ₁.contDiff.add contDiff_const)
    have hG₂ : ContDiff ℝ ∞ (fun v => elemLift g₂ a₂ b₂ (Λ₂ v + c₂)) :=
      (h₂.1 a₂ b₂).comp (Λ₂.contDiff.add contDiff_const)
    have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hG₁ hG₂ v (n := k) (by exact_mod_cast le_top)
    have hterm : ∀ l ∈ Finset.range (k + 1), (A₁ ^ N * A₂ ^ N) * ((k.choose l : ℝ) *
        ‖iteratedFDeriv ℝ l (fun v => elemLift g₁ a₁ b₁ (Λ₁ v + c₁)) v‖ *
        ‖iteratedFDeriv ℝ (k - l) (fun v => elemLift g₂ a₂ b₂ (Λ₂ v + c₂)) v‖) ≤
        (k.choose l : ℝ) * (‖Λ₁‖ ^ l * M₁ l) * (‖Λ₂‖ ^ (k - l) * M₂ (k - l)) := by
      intro l _
      have e₁ := deriv_affine_bound _ (h₁.1 a₁ b₁) Λ₁ c₁ l v
      have e₂ := deriv_affine_bound _ (h₂.1 a₂ b₂) Λ₂ c₂ (k - l) v
      have f₁ := hM₁ l a₁ b₁ (Λ₁ v + c₁)
      have f₂ := hM₂ (k - l) a₂ b₂ (Λ₂ v + c₂)
      have hM₁0 : 0 ≤ M₁ l := le_trans (by positivity) f₁
      have hM₂0 : 0 ≤ M₂ (k - l) := le_trans (by positivity) f₂
      have t₁ : A₁ ^ N * ‖iteratedFDeriv ℝ l (fun v => elemLift g₁ a₁ b₁ (Λ₁ v + c₁)) v‖ ≤
          ‖Λ₁‖ ^ l * M₁ l := by
        calc _ ≤ A₁ ^ N * (‖Λ₁‖ ^ l * ‖iteratedFDeriv ℝ l (elemLift g₁ a₁ b₁) (Λ₁ v + c₁)‖) :=
              mul_le_mul_of_nonneg_left e₁ (by positivity)
          _ = ‖Λ₁‖ ^ l * (A₁ ^ N * ‖iteratedFDeriv ℝ l (elemLift g₁ a₁ b₁) (Λ₁ v + c₁)‖) := by ring
          _ ≤ ‖Λ₁‖ ^ l * M₁ l := mul_le_mul_of_nonneg_left f₁ (by positivity)
      have t₂ : A₂ ^ N * ‖iteratedFDeriv ℝ (k - l) (fun v => elemLift g₂ a₂ b₂ (Λ₂ v + c₂)) v‖ ≤
          ‖Λ₂‖ ^ (k - l) * M₂ (k - l) := by
        calc _ ≤ A₂ ^ N * (‖Λ₂‖ ^ (k - l) *
              ‖iteratedFDeriv ℝ (k - l) (elemLift g₂ a₂ b₂) (Λ₂ v + c₂)‖) :=
              mul_le_mul_of_nonneg_left e₂ (by positivity)
          _ = ‖Λ₂‖ ^ (k - l) *
              (A₂ ^ N * ‖iteratedFDeriv ℝ (k - l) (elemLift g₂ a₂ b₂) (Λ₂ v + c₂)‖) := by ring
          _ ≤ ‖Λ₂‖ ^ (k - l) * M₂ (k - l) := mul_le_mul_of_nonneg_left f₂ (by positivity)
      calc (A₁ ^ N * A₂ ^ N) * ((k.choose l : ℝ) *
            ‖iteratedFDeriv ℝ l (fun v => elemLift g₁ a₁ b₁ (Λ₁ v + c₁)) v‖ *
            ‖iteratedFDeriv ℝ (k - l) (fun v => elemLift g₂ a₂ b₂ (Λ₂ v + c₂)) v‖)
          = (k.choose l : ℝ) *
            (A₁ ^ N * ‖iteratedFDeriv ℝ l (fun v => elemLift g₁ a₁ b₁ (Λ₁ v + c₁)) v‖) *
            (A₂ ^ N * ‖iteratedFDeriv ℝ (k - l) (fun v => elemLift g₂ a₂ b₂ (Λ₂ v + c₂)) v‖) := by
            ring
        _ ≤ (k.choose l : ℝ) * (‖Λ₁‖ ^ l * M₁ l) * (‖Λ₂‖ ^ (k - l) * M₂ (k - l)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left t₁ (by positivity)) t₂ (by positivity)
              (mul_nonneg (by positivity) (mul_nonneg (by positivity) hM₁0))
    calc ‖a‖ ^ j * ‖v.1‖ ^ i * ‖iteratedFDeriv ℝ k
          (fun v => elemLift g₁ a₁ b₁ (Λ₁ v + c₁) * elemLift g₂ a₂ b₂ (Λ₂ v + c₂)) v‖
        ≤ (K ^ N * (A₁ ^ N * A₂ ^ N)) * ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) *
            ‖iteratedFDeriv ℝ l (fun v => elemLift g₁ a₁ b₁ (Λ₁ v + c₁)) v‖ *
            ‖iteratedFDeriv ℝ (k - l) (fun v => elemLift g₂ a₂ b₂ (Λ₂ v + c₂)) v‖ :=
          mul_le_mul (hS.trans hSK) hL (norm_nonneg _)
            (mul_nonneg (pow_nonneg hK N) (by positivity))
      _ = K ^ N * ∑ l ∈ Finset.range (k + 1), (A₁ ^ N * A₂ ^ N) * ((k.choose l : ℝ) *
            ‖iteratedFDeriv ℝ l (fun v => elemLift g₁ a₁ b₁ (Λ₁ v + c₁)) v‖ *
            ‖iteratedFDeriv ℝ (k - l) (fun v => elemLift g₂ a₂ b₂ (Λ₂ v + c₂)) v‖) := by
          rw [mul_assoc, Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (pow_nonneg hK N)

end pull

theorem sec_spec {m n r s : ℕ} {d : Fin s → ℕ} {m' n' r' s' : ℕ} {d' : Fin s' → ℕ}
    (p : Multiplicative (ElemGroup m n r s d) →* Multiplicative (ElemGroup m' n' r' s' d'))
    (L : (Fin m' → ℝ) × (Fin n' → ℝ) →L[ℝ] (Fin m → ℝ) × (Fin n → ℝ))
    (hL : ∀ v : (Fin m' → ℝ) × (Fin n' → ℝ),
        p (Multiplicative.ofAdd
            ((L v).1, fun j => (((L v).2 j : ℝ) : UnitAddCircle), 0, 0)) =
          Multiplicative.ofAdd (v.1, fun j => ((v.2 j : ℝ) : UnitAddCircle), 0, 0))
    (w : Fin r' → ElemGroup m n r s d)
    (hw : ∀ i, p (Multiplicative.ofAdd (w i)) = Multiplicative.ofAdd
      ((0, 0, Pi.single i 1, 0) : ElemGroup m' n' r' s' d'))
    (x : ElemGroup m' n' r' s' d') :
    (AddMonoidHom.toMultiplicative.symm p) (secA L w x) = (x.1, 0, x.2.2.1, 0) := by
  set pA : ElemGroup m n r s d →+ ElemGroup m' n' r' s' d' :=
    AddMonoidHom.toMultiplicative.symm p with hpA_def
  have hpA : ∀ x, pA x = Multiplicative.toAdd (p (Multiplicative.ofAdd x)) := fun x => rfl
  rw [secA_apply, map_add]
  have h1 : pA (vecSec L x.1) = (x.1, 0, 0, 0) := by
    rw [hpA]
    change Multiplicative.toAdd (p (Multiplicative.ofAdd ((L (x.1, 0)).1,
      fun j => (((L (x.1, 0)).2 j : ℝ) : UnitAddCircle), 0, 0))) = _
    rw [hL (x.1, 0)]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    funext j
    simp
  have h3 : ∀ i, pA (w i) = (0, 0, Pi.single i 1, 0) := fun i => by
    rw [hpA]; exact congrArg Multiplicative.toAdd (hw i)
  have h2 : pA (latSec w x.2.2.1) = (0, 0, x.2.2.1, 0) := by
    change pA (∑ i, x.2.2.1 i • w i) = _
    rw [map_sum]
    simp only [map_zsmul, h3]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Prod.fst_sum]
    · funext k
      simp [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  rw [h1, h2]
  simp

theorem zsmul_sum_bound {G : Type*} [SeminormedAddCommGroup G] {k : ℕ} (a : Fin k → ℤ)
    (v : Fin k → G) : ‖∑ i, a i • v i‖ ≤ ‖a‖ * ∑ i, ‖v i‖ := by
  calc ‖∑ i, a i • v i‖ ≤ ∑ i, ‖a i • v i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖a‖ * ‖v i‖ := Finset.sum_le_sum fun i _ =>
        (norm_zsmul_le (a i) (v i)).trans
          (mul_le_mul_of_nonneg_right (norm_le_pi_norm a i) (norm_nonneg _))
    _ = ‖a‖ * ∑ i, ‖v i‖ := (Finset.mul_sum _ _ _).symm

theorem sec_bound {m n r s : ℕ} {d : Fin s → ℕ} {m' n' r' s' : ℕ} {d' : Fin s' → ℕ}
    (L : (Fin m' → ℝ) × (Fin n' → ℝ) →L[ℝ] (Fin m → ℝ) × (Fin n → ℝ))
    (w₀ : Fin r' → ElemGroup m n r s d) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ x : ElemGroup m' n' r' s' d',
      ‖(secA L w₀ x).1‖ + ‖(secA L w₀ x).2.2.1‖ ≤ K₀ * (‖x.1‖ + ‖x.2.2.1‖) := by
  refine ⟨‖L‖ + ∑ i, ‖(w₀ i).1‖ + ∑ i, ‖(w₀ i).2.2.1‖, by positivity, fun x => ?_⟩
  rw [secA_apply]
  have hv1 : ‖(vecSec (r := r) (s := s) (d := d) L x.1).1‖ ≤ ‖L‖ * ‖x.1‖ := by
    change ‖(L (x.1, 0)).1‖ ≤ _
    calc _ ≤ ‖L (x.1, 0)‖ := norm_fst_le _
      _ ≤ ‖L‖ * ‖((x.1, 0) : (Fin m' → ℝ) × (Fin n' → ℝ))‖ := L.le_opNorm _
      _ = ‖L‖ * ‖x.1‖ := by rw [Prod.norm_def]; simp
  have hv2 : (vecSec (r := r) (s := s) (d := d) L x.1).2.2.1 = 0 := rfl
  have hl1 : ‖(latSec w₀ x.2.2.1).1‖ ≤ ‖x.2.2.1‖ * ∑ i, ‖(w₀ i).1‖ := by
    change ‖(∑ i, x.2.2.1 i • w₀ i).1‖ ≤ _
    rw [Prod.fst_sum]
    simp only [Prod.smul_fst]
    exact zsmul_sum_bound _ _
  have hl2 : ‖(latSec w₀ x.2.2.1).2.2.1‖ ≤ ‖x.2.2.1‖ * ∑ i, ‖(w₀ i).2.2.1‖ := by
    change ‖(∑ i, x.2.2.1 i • w₀ i).2.2.1‖ ≤ _
    rw [Prod.snd_sum, Prod.snd_sum, Prod.fst_sum]
    simp only [Prod.smul_fst, Prod.smul_snd]
    exact zsmul_sum_bound _ _
  have e1 := norm_add_le (vecSec (r := r) (s := s) (d := d) L x.1).1 (latSec w₀ x.2.2.1).1
  have e2 := norm_add_le (vecSec (r := r) (s := s) (d := d) L x.1).2.2.1 (latSec w₀ x.2.2.1).2.2.1
  rw [hv2, norm_zero] at e2
  change ‖(vecSec L x.1).1 + (latSec w₀ x.2.2.1).1‖ +
    ‖(vecSec L x.1).2.2.1 + (latSec w₀ x.2.2.1).2.2.1‖ ≤ _
  rw [hv2]
  have p1 : 0 ≤ ‖x.1‖ := norm_nonneg _
  have p2 : 0 ≤ ‖x.2.2.1‖ := norm_nonneg _
  have p3 : 0 ≤ ‖L‖ := norm_nonneg _
  have p4 : 0 ≤ ∑ i, ‖(w₀ i).1‖ := by positivity
  have p5 : 0 ≤ ∑ i, ‖(w₀ i).2.2.1‖ := by positivity
  nlinarith [mul_nonneg p3 p2, mul_nonneg p4 p1, mul_nonneg p5 p1]

theorem surj {m n r s : ℕ} {d : Fin s → ℕ} {m' n' r' s' : ℕ} {d' : Fin s' → ℕ}
    (hd' : ∀ i, d' i ≠ 0)
    [MeasurableSpace (Multiplicative (ElemGroup m n r s d))]
    [BorelSpace (Multiplicative (ElemGroup m n r s d))]
    (p : Multiplicative (ElemGroup m n r s d) →* Multiplicative (ElemGroup m' n' r' s' d'))
    (hpc : Continuous p) (hpo : IsOpenMap p) (hps : Function.Surjective p)
    (ν : Measure p.ker) [ν.IsHaarMeasure]
    (T : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m' n' r' s' d')
    (hT : ∀ (g : ElemSchwartz m n r s d) (y : Multiplicative (ElemGroup m n r s d)),
        Integrable (fun l : p.ker =>
          g.toFun (Multiplicative.toAdd (y * (l : Multiplicative (ElemGroup m n r s d))))) ν ∧
        (T g).toFun (Multiplicative.toAdd (p y)) =
          ∫ l : p.ker,
            g.toFun (Multiplicative.toAdd (y * (l : Multiplicative (ElemGroup m n r s d)))) ∂ν) :
    Function.Surjective T := by
  classical
  intro s0
  obtain ⟨L, hL⟩ := linearSection p hpc hpo
  choose w₀ hw₀ using fun i : Fin r' =>
    hps (Multiplicative.ofAdd ((0, 0, Pi.single i 1, 0) : ElemGroup m' n' r' s' d'))
  let w : Fin r' → ElemGroup m n r s d := fun i => Multiplicative.toAdd (w₀ i)
  have hw : ∀ i, p (Multiplicative.ofAdd (w i)) = Multiplicative.ofAdd
      ((0, 0, Pi.single i 1, 0) : ElemGroup m' n' r' s' d') := hw₀
  let σ : ElemGroup m' n' r' s' d' →+ ElemGroup m n r s d := secA L w
  let pA : ElemGroup m n r s d →+ ElemGroup m' n' r' s' d' := AddMonoidHom.toMultiplicative.symm p
  have hσ : ∀ x, pA (σ x) = (x.1, 0, x.2.2.1, 0) := sec_spec p L hL w hw
  let ρ : ElemGroup m n r s d →+ ElemGroup m n r s d := AddMonoidHom.id _ - σ.comp pA
  let rm : Multiplicative (ElemGroup m n r s d) →* Multiplicative (ElemGroup m n r s d) :=
    AddMonoidHom.toMultiplicative ρ
  let cm : Multiplicative (ElemGroup m' n' r' s' d') →* Multiplicative (ElemGroup 0 n' 0 s' d') :=
    AddMonoidHom.toMultiplicative cA
  have hρc : Continuous rm := continuous_id.sub ((continuous_secA L w).comp hpc)
  have hcc : Continuous cm := continuous_cA
  have hpr : ∀ z, Multiplicative.toAdd (p (rm z)) = jf (cA (Multiplicative.toAdd (p z))) := by
    intro z
    change pA (Multiplicative.toAdd z - σ (pA (Multiplicative.toAdd z))) = _
    rw [map_sub, hσ]
    exact Prod.ext (sub_self _) (Prod.ext (sub_zero _) (Prod.ext (sub_self _) (sub_zero _)))
  have hrker : ∀ l : p.ker, rm l = l := by
    intro l
    have hl : p l = 1 := (MonoidHom.mem_ker).mp l.2
    change Multiplicative.ofAdd (Multiplicative.toAdd (l : Multiplicative (ElemGroup m n r s d)) -
      σ (pA (Multiplicative.toAdd (l : Multiplicative (ElemGroup m n r s d))))) = l
    rw [show pA (Multiplicative.toAdd (l : Multiplicative (ElemGroup m n r s d))) = 0 from
      congrArg Multiplicative.toAdd hl, map_zero, sub_zero]
    rfl
  -- a positive test function and its fibre integral
  obtain ⟨θ, hθ⟩ := exists_pos_elemSchwartz m n r s d
  have hηne : ∀ w' : ElemGroup m' n' r' s' d', (T θ).toFun w' ≠ 0 := by
    intro w'
    obtain ⟨y, hy⟩ := hps (Multiplicative.ofAdd w')
    change (T θ).toFun (Multiplicative.toAdd (Multiplicative.ofAdd w')) ≠ 0
    rw [← hy, (hT θ y).2]
    intro h0
    have hfi := (hT θ y).1
    have hre : Integrable (fun l : p.ker =>
        (θ.toFun (Multiplicative.toAdd (y * (l : Multiplicative (ElemGroup m n r s d))))).re) ν :=
      hfi.re
    have hpos : 0 < ∫ l : p.ker,
        (θ.toFun (Multiplicative.toAdd (y * (l : Multiplicative (ElemGroup m n r s d))))).re ∂ν := by
      rw [integral_pos_iff_support_of_nonneg (fun l => ?_) hre]
      · rw [show Function.support (fun l : p.ker =>
            (θ.toFun (Multiplicative.toAdd (y * (l : Multiplicative (ElemGroup m n r s d))))).re) =
            Set.univ from Set.eq_univ_of_forall fun l => by
              obtain ⟨t, ht, he⟩ :=
                hθ (Multiplicative.toAdd (y * (l : Multiplicative (ElemGroup m n r s d))))
              rw [Function.mem_support, he, Complex.ofReal_re]; exact ht.ne']
        exact isOpen_univ.measure_pos ν Set.univ_nonempty
      · obtain ⟨t, ht, he⟩ :=
          hθ (Multiplicative.toAdd (y * (l : Multiplicative (ElemGroup m n r s d))))
        change 0 ≤ (θ.toFun _).re
        rw [he, Complex.ofReal_re]; exact ht.le
    have h2 : ∫ l : p.ker,
        (θ.toFun (Multiplicative.toAdd (y * (l : Multiplicative (ElemGroup m n r s d))))).re ∂ν =
        (∫ l : p.ker,
          θ.toFun (Multiplicative.toAdd (y * (l : Multiplicative (ElemGroup m n r s d)))) ∂ν).re :=
      integral_re hfi
    rw [h2, h0, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  -- the inverse of the fibre integral of θ on the compact factors
  let κf : ElemGroup 0 n' 0 s' d' → ℂ := fun u => ((T θ).toFun (jf u))⁻¹
  have hκ : IsRapidDecay κf := isRapidDecay_of_compact hd' κf (fun a b => by
    have hη := (isRapidDecay_elemSchwartz_toFun (T θ)).1 0 b
    have : elemLift κf a b =
        fun xt => (elemLift (T θ).toFun 0 b ((0 : Fin m' → ℝ), xt.2))⁻¹ := rfl
    rw [this]
    exact (hη.comp (contDiff_const.prodMk contDiff_snd)).inv (fun xt => hηne _))
  let κ : ElemSchwartz 0 n' 0 s' d' := ⟨κf, Submodule.subset_span hκ⟩
  have hs₁rd : IsRapidDecay (fun z : ElemGroup m' n' r' s' d' =>
      s0.toFun (AddMonoidHom.id _ z) * κf (cA z)) := by
    refine isRapidDecay_mul_pull (AddMonoidHom.id _) cA continuous_id continuous_cA 1 zero_le_one
      (fun z => ?_) s0.toFun κf (isRapidDecay_elemSchwartz_toFun s0) hκ
    have q1 : 0 ≤ ‖z.1‖ + ‖z.2.2.1‖ := by positivity
    have q2 : 0 ≤ ‖(cA z).1‖ + ‖(cA z).2.2.1‖ := by positivity
    change ‖z.1‖ + ‖z.2.2.1‖ ≤ 1 * ((1 + (‖z.1‖ + ‖z.2.2.1‖)) * (1 + (‖(cA z).1‖ + ‖(cA z).2.2.1‖)))
    nlinarith [mul_nonneg q1 q2]
  let s₁ : ElemSchwartz m' n' r' s' d' := ⟨_, Submodule.subset_span hs₁rd⟩
  have hs₁ : ∀ z : Multiplicative (ElemGroup m' n' r' s' d'), s₁.toFun (Multiplicative.toAdd z) =
      s0.toFun (Multiplicative.toAdd ((MonoidHom.id _) z)) * κ.toFun (Multiplicative.toAdd (cm z)) :=
    fun z => rfl
  obtain ⟨K₀, hK₀, hK₀b⟩ := sec_bound L w
  have htrd : IsRapidDecay (fun z : ElemGroup m n r s d => s₁.toFun (pA z) * θ.toFun (ρ z)) := by
    refine isRapidDecay_mul_pull pA ρ hpc hρc (K₀ + 1) (by positivity) (fun z => ?_) s₁.toFun
      θ.toFun (isRapidDecay_elemSchwartz_toFun s₁) (isRapidDecay_elemSchwartz_toFun θ)
    have hz : z = σ (pA z) + ρ z := by
      change z = σ (pA z) + (z - σ (pA z)); abel
    have e1 : ‖z.1‖ ≤ ‖(σ (pA z)).1‖ + ‖(ρ z).1‖ := by
      conv_lhs => rw [hz]
      exact norm_add_le _ _
    have e2 : ‖z.2.2.1‖ ≤ ‖(σ (pA z)).2.2.1‖ + ‖(ρ z).2.2.1‖ := by
      conv_lhs => rw [hz]
      exact norm_add_le _ _
    have e3 := hK₀b (pA z)
    have q1 : 0 ≤ ‖(pA z).1‖ + ‖(pA z).2.2.1‖ := by positivity
    have q2 : 0 ≤ ‖(ρ z).1‖ + ‖(ρ z).2.2.1‖ := by positivity
    nlinarith [mul_nonneg q1 q2, mul_nonneg hK₀ q1, mul_nonneg hK₀ q2, mul_nonneg (mul_nonneg hK₀ q1) q2]
  let t : ElemSchwartz m n r s d := ⟨_, Submodule.subset_span htrd⟩
  have ht : ∀ z : Multiplicative (ElemGroup m n r s d), t.toFun (Multiplicative.toAdd z) =
      s₁.toFun (Multiplicative.toAdd (p z)) * θ.toFun (Multiplicative.toAdd (rm z)) := fun z => rfl
  refine ⟨t, ?_⟩
  apply Subtype.ext
  funext w'
  obtain ⟨y, hy⟩ := hps (Multiplicative.ofAdd w')
  have key : (T t).toFun (Multiplicative.toAdd (p y)) = s0.toFun (Multiplicative.toAdd (p y)) := by
    rw [(hT t y).2]
    have h1 : ∀ l : p.ker, t.toFun (Multiplicative.toAdd (y * (l : Multiplicative (ElemGroup m n r s d)))) =
        s₁.toFun (Multiplicative.toAdd (p y)) *
          θ.toFun (Multiplicative.toAdd (rm y * (l : Multiplicative (ElemGroup m n r s d)))) := by
      intro l
      rw [ht, map_mul p y, map_mul rm y, hrker l, (MonoidHom.mem_ker).mp l.2, mul_one]
    rw [integral_congr_ae (Filter.Eventually.of_forall h1), integral_const_mul, ← (hT θ (rm y)).2,
      hs₁, hpr]
    change s0.toFun (Multiplicative.toAdd (p y)) *
        ((T θ).toFun (jf (cA (Multiplicative.toAdd (p y)))))⁻¹ *
        (T θ).toFun (jf (cA (Multiplicative.toAdd (p y)))) = _
    rw [mul_assoc, inv_mul_cancel₀ (hηne _), mul_one]
  rw [hy] at key
  exact key

end Sol_MasulloGRH_elemSchwartz_fiberIntegral

open MasulloGRH Sol_MasulloGRH_elemSchwartz_fiberIntegral in
theorem solution
    {m n r s : ℕ} {d : Fin s → ℕ} {m' n' r' s' : ℕ} {d' : Fin s' → ℕ}
    (hd : ∀ i, d i ≠ 0) (hd' : ∀ i, d' i ≠ 0)
    [MeasurableSpace (Multiplicative (ElemGroup m n r s d))]
    [BorelSpace (Multiplicative (ElemGroup m n r s d))]
    (p : Multiplicative (ElemGroup m n r s d) →* Multiplicative (ElemGroup m' n' r' s' d'))
    (hpc : Continuous p) (hpo : IsOpenMap p) (hps : Function.Surjective p)
    (ν : Measure p.ker) [ν.IsHaarMeasure] :
    ∃ T : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m' n' r' s' d',
      Continuous T ∧ Function.Surjective T ∧
      ∀ (g : ElemSchwartz m n r s d) (y : Multiplicative (ElemGroup m n r s d)),
        Integrable (fun l : p.ker =>
          g.toFun (Multiplicative.toAdd (y * (l : Multiplicative (ElemGroup m n r s d))))) ν ∧
        (T g).toFun (Multiplicative.toAdd (p y)) =
          ∫ l : p.ker,
            g.toFun (Multiplicative.toAdd (y * (l : Multiplicative (ElemGroup m n r s d)))) ∂ν := by
  obtain ⟨T, hTc, hT⟩ := elemSchwartz_fiberIntegral_continuous hd hd' p hpc hpo hps ν
  exact ⟨T, hTc, surj hd' p hpc hpo hps ν T hT, hT⟩
