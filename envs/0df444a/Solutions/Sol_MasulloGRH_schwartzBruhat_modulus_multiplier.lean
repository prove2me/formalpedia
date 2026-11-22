-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_modulus_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T20:04:28.631876+00:00
-- url     : https://prove2.me/submissions/10a80d96-916a-4fa6-b9ee-2de9467c59a4

import Theorems.Thm_MasulloGRH_elemSchwartz_continuous_of_seminorm_bound
import Theorems.Thm_MasulloGRH_isRapidDecay_elemSchwartz_toFun
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

universe u


namespace HBoundAux

open Real

/-- uniform bound on the `j`-th derivative -/
def Bdd (f : ℝ → ℝ) (j : ℕ) : Prop := ∃ C, ∀ s, ‖iteratedFDeriv ℝ j f s‖ ≤ C

lemma bdd_mul {f g : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) (n : ℕ)
    (bf : ∀ j ≤ n, Bdd f j) (bg : ∀ j ≤ n, Bdd g j) : ∀ j ≤ n, Bdd (fun s => f s * g s) j := by
  intro j hj
  choose! Cf hCf using bf
  choose! Cg hCg using bg
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Cf i * Cg (j - i), fun s => ?_⟩
  refine (norm_iteratedFDeriv_mul_le hf hg s (by exact_mod_cast le_top)).trans ?_
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have h1 := hCf i (hi'.trans hj) s
  have h2 := hCg (j - i) ((Nat.sub_le _ _).trans hj) s
  have hc : (0 : ℝ) ≤ j.choose i := Nat.cast_nonneg _
  have := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f s‖ * ‖iteratedFDeriv ℝ (j - i) g s‖
      = (j.choose i : ℝ) * (‖iteratedFDeriv ℝ i f s‖ * ‖iteratedFDeriv ℝ (j - i) g s‖) := by ring
    _ ≤ (j.choose i : ℝ) * (Cf i * Cg (j - i)) := mul_le_mul_of_nonneg_left this hc
    _ = _ := by ring

lemma bdd_add {f g : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) (j : ℕ)
    (bf : Bdd f j) (bg : Bdd g j) : Bdd (fun s => f s + g s) j := by
  obtain ⟨C₁, h₁⟩ := bf
  obtain ⟨C₂, h₂⟩ := bg
  refine ⟨C₁ + C₂, fun s => ?_⟩
  have : iteratedFDeriv ℝ j (fun s => f s + g s) s = iteratedFDeriv ℝ j f s + iteratedFDeriv ℝ j g s :=
    iteratedFDeriv_add_apply (hf.contDiffAt.of_le (by exact_mod_cast le_top))
      (hg.contDiffAt.of_le (by exact_mod_cast le_top))
  rw [this]
  exact (norm_add_le _ _).trans (add_le_add (h₁ s) (h₂ s))

lemma bdd_const_mul {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (c : ℝ) (j : ℕ) (bf : Bdd f j) :
    Bdd (fun s => c * f s) j := by
  obtain ⟨C, h⟩ := bf
  refine ⟨‖c‖ * C, fun s => ?_⟩
  have : iteratedFDeriv ℝ j (fun s => c * f s) s = c • iteratedFDeriv ℝ j f s := by
    have hc : ContDiffAt ℝ j f s := hf.contDiffAt.of_le (by exact_mod_cast le_top)
    have := iteratedFDeriv_const_smul_apply (a := c) hc
    exact this
  rw [this, norm_smul]
  exact mul_le_mul_of_nonneg_left (h s) (norm_nonneg _)

/-- the derivative step: bounds at order `j` for `deriv f` give bounds at order `j+1` for `f` -/
lemma bdd_succ {f : ℝ → ℝ} (j : ℕ) (b : Bdd (deriv f) j) : Bdd f (j + 1) := by
  obtain ⟨C, h⟩ := b
  refine ⟨C, fun s => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ',
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact h s

section main

variable (b₁ b₂ : ℝ)

/-- `h(s) = 1/(e^{b₁ s} + e^{b₂ s})` -/
noncomputable def hh (s : ℝ) : ℝ := (exp (b₁ * s) + exp (b₂ * s))⁻¹
noncomputable def pp (s : ℝ) : ℝ := exp (b₁ * s) * hh b₁ b₂ s
noncomputable def qq (s : ℝ) : ℝ := exp (b₂ * s) * hh b₁ b₂ s

lemma D_pos (s : ℝ) : 0 < exp (b₁ * s) + exp (b₂ * s) := by positivity

lemma e_cd (b : ℝ) : ContDiff ℝ ⊤ fun s : ℝ => exp (b * s) :=
  contDiff_exp.comp (contDiff_const.mul contDiff_id)

lemma hh_cd : ContDiff ℝ ⊤ (hh b₁ b₂) :=
  ((e_cd b₁).add (e_cd b₂)).inv fun s => (D_pos b₁ b₂ s).ne'

lemma pp_cd : ContDiff ℝ ⊤ (pp b₁ b₂) := (e_cd b₁).mul (hh_cd b₁ b₂)
lemma qq_cd : ContDiff ℝ ⊤ (qq b₁ b₂) := (e_cd b₂).mul (hh_cd b₁ b₂)

lemma hasDerivAt_e (b s : ℝ) : HasDerivAt (fun s : ℝ => exp (b * s)) (b * exp (b * s)) s := by
  have := ((hasDerivAt_id s).const_mul b).exp
  simpa [mul_comm] using this

lemma deriv_hh : deriv (hh b₁ b₂) = fun s =>
    ((-b₁) * pp b₁ b₂ s + (-b₂) * qq b₁ b₂ s) * hh b₁ b₂ s := by
  funext s
  have hD := (hasDerivAt_e b₁ s).add (hasDerivAt_e b₂ s)
  have := hD.inv (D_pos b₁ b₂ s).ne'
  rw [show deriv (hh b₁ b₂) s = _ from this.deriv]
  simp only [pp, qq, hh, Pi.add_apply]
  have := (D_pos b₁ b₂ s).ne'
  field_simp
  ring

lemma deriv_pp : deriv (pp b₁ b₂) = fun s =>
    b₁ * pp b₁ b₂ s + (-1) * (pp b₁ b₂ s * (b₁ * pp b₁ b₂ s + b₂ * qq b₁ b₂ s)) := by
  funext s
  have hh' : HasDerivAt (hh b₁ b₂) (((-b₁) * pp b₁ b₂ s + (-b₂) * qq b₁ b₂ s) * hh b₁ b₂ s) s := by
    have := ((hh_cd b₁ b₂).differentiable (by simp)).differentiableAt (x := s) |>.hasDerivAt
    rwa [deriv_hh] at this
  have := (hasDerivAt_e b₁ s).mul hh'
  rw [show deriv (pp b₁ b₂) s = _ from this.deriv]
  simp only [pp, qq]
  ring

lemma deriv_qq : deriv (qq b₁ b₂) = fun s =>
    b₂ * qq b₁ b₂ s + (-1) * (qq b₁ b₂ s * (b₁ * pp b₁ b₂ s + b₂ * qq b₁ b₂ s)) := by
  funext s
  have hh' : HasDerivAt (hh b₁ b₂) (((-b₁) * pp b₁ b₂ s + (-b₂) * qq b₁ b₂ s) * hh b₁ b₂ s) s := by
    have := ((hh_cd b₁ b₂).differentiable (by simp)).differentiableAt (x := s) |>.hasDerivAt
    rwa [deriv_hh] at this
  have := (hasDerivAt_e b₂ s).mul hh'
  rw [show deriv (qq b₁ b₂) s = _ from this.deriv]
  simp only [pp, qq]
  ring

lemma one_le_D (hb₁ : b₁ ≤ 0) (hb₂ : 0 ≤ b₂) (s : ℝ) : 1 ≤ exp (b₁ * s) + exp (b₂ * s) := by
  rcases le_total 0 s with hs | hs
  · have : 1 ≤ exp (b₂ * s) := one_le_exp (mul_nonneg hb₂ hs)
    linarith [exp_pos (b₁ * s)]
  · have : 1 ≤ exp (b₁ * s) := one_le_exp (mul_nonneg_of_nonpos_of_nonpos hb₁ hs)
    linarith [exp_pos (b₂ * s)]

lemma bdd0 {f : ℝ → ℝ} (h : ∀ s, |f s| ≤ 1) : Bdd f 0 :=
  ⟨1, fun s => by rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]; exact h s⟩

theorem hh_bdd (hb₁ : b₁ ≤ 0) (hb₂ : 0 ≤ b₂) : ∀ j, Bdd (hh b₁ b₂) j := by
  have hD := D_pos b₁ b₂
  have h0h : ∀ s, |hh b₁ b₂ s| ≤ 1 := fun s => by
    show |(exp (b₁ * s) + exp (b₂ * s))⁻¹| ≤ 1
    rw [abs_of_pos (inv_pos.2 (hD s))]
    exact inv_le_one_of_one_le₀ (one_le_D b₁ b₂ hb₁ hb₂ s)
  have h0p : ∀ s, |pp b₁ b₂ s| ≤ 1 := fun s => by
    have : pp b₁ b₂ s = exp (b₁ * s) / (exp (b₁ * s) + exp (b₂ * s)) := by
      simp [pp, hh, div_eq_mul_inv]
    rw [this, abs_of_pos (div_pos (exp_pos _) (hD s)), div_le_one (hD s)]
    linarith [exp_pos (b₂ * s)]
  have h0q : ∀ s, |qq b₁ b₂ s| ≤ 1 := fun s => by
    have : qq b₁ b₂ s = exp (b₂ * s) / (exp (b₁ * s) + exp (b₂ * s)) := by
      simp [qq, hh, div_eq_mul_inv]
    rw [this, abs_of_pos (div_pos (exp_pos _) (hD s)), div_le_one (hD s)]
    linarith [exp_pos (b₁ * s)]
  have ch := hh_cd b₁ b₂
  have cp := pp_cd b₁ b₂
  have cq := qq_cd b₁ b₂
  -- the linear combination `b₁ p + b₂ q` and friends
  have cL : ∀ c₁ c₂ : ℝ, ContDiff ℝ ⊤ fun s => c₁ * pp b₁ b₂ s + c₂ * qq b₁ b₂ s :=
    fun c₁ c₂ => (contDiff_const.mul cp).add (contDiff_const.mul cq)
  have key : ∀ n, ∀ j ≤ n, Bdd (hh b₁ b₂) j ∧ Bdd (pp b₁ b₂) j ∧ Bdd (qq b₁ b₂) j := by
    intro n
    induction n with
    | zero =>
      intro j hj
      rw [Nat.le_zero.1 hj]
      exact ⟨bdd0 h0h, bdd0 h0p, bdd0 h0q⟩
    | succ n ih =>
      have bh : ∀ j ≤ n, Bdd (hh b₁ b₂) j := fun j hj => (ih j hj).1
      have bp : ∀ j ≤ n, Bdd (pp b₁ b₂) j := fun j hj => (ih j hj).2.1
      have bq : ∀ j ≤ n, Bdd (qq b₁ b₂) j := fun j hj => (ih j hj).2.2
      have bL : ∀ c₁ c₂ : ℝ, ∀ j ≤ n, Bdd (fun s => c₁ * pp b₁ b₂ s + c₂ * qq b₁ b₂ s) j :=
        fun c₁ c₂ j hj => bdd_add (contDiff_const.mul cp) (contDiff_const.mul cq) j
          (bdd_const_mul cp c₁ j (bp j hj)) (bdd_const_mul cq c₂ j (bq j hj))
      intro j hj
      rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
      · exact ih j (Nat.lt_succ_iff.1 hj')
      have hjn : j = n + 1 := le_antisymm hj hj'
      subst hjn
      refine ⟨bdd_succ n ?_, bdd_succ n ?_, bdd_succ n ?_⟩
      · rw [deriv_hh]
        exact bdd_mul (cL _ _) ch n (bL _ _) bh n le_rfl
      · rw [deriv_pp]
        exact bdd_add (contDiff_const.mul cp) (contDiff_const.mul (cp.mul (cL _ _))) n
          (bdd_const_mul cp _ n (bp n le_rfl))
          (bdd_const_mul (cp.mul (cL _ _)) _ n (bdd_mul cp (cL _ _) n bp (bL _ _) n le_rfl))
      · rw [deriv_qq]
        exact bdd_add (contDiff_const.mul cq) (contDiff_const.mul (cq.mul (cL _ _))) n
          (bdd_const_mul cq _ n (bq n le_rfl))
          (bdd_const_mul (cq.mul (cL _ _)) _ n (bdd_mul cq (cL _ _) n bq (bL _ _) n le_rfl))
  exact fun j => (key j j le_rfl).1

end main

/-- the multiplier `x ↦ h(Λ x + c)` (complex valued) is smooth with bounded derivatives,
uniformly in `c` -/
theorem mult_bdd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (b₁ b₂ : ℝ)
    (hb₁ : b₁ ≤ 0) (hb₂ : 0 ≤ b₂) (Λ : E →L[ℝ] ℝ) :
    (∀ c : ℝ, ContDiff ℝ ⊤ (fun x => ((hh b₁ b₂ (Λ x + c) : ℝ) : ℂ))) ∧
      ∀ j, ∃ C, 0 ≤ C ∧ ∀ (c : ℝ) x,
        ‖iteratedFDeriv ℝ j (fun x => ((hh b₁ b₂ (Λ x + c) : ℝ) : ℂ)) x‖ ≤ C := by
  have hc : ∀ c : ℝ, ContDiff ℝ ⊤ fun t => hh b₁ b₂ (t + c) := fun c =>
    (hh_cd b₁ b₂).comp (contDiff_id.add contDiff_const)
  have hcomp : ∀ c : ℝ, ContDiff ℝ ⊤ ((fun t => hh b₁ b₂ (t + c)) ∘ Λ) := fun c =>
    (hc c).comp Λ.contDiff
  refine ⟨fun c => Complex.ofRealCLM.contDiff.comp (hcomp c), fun j => ?_⟩
  obtain ⟨C, hC⟩ := hh_bdd b₁ b₂ hb₁ hb₂ j
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨‖Complex.ofRealCLM‖ * (C * ‖Λ‖ ^ j), by positivity, fun c x => ?_⟩
  have e1 := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left (n := j) (x := x)
    (hcomp c).contDiffAt (by exact_mod_cast le_top)
  have e2 : iteratedFDeriv ℝ j ((fun t => hh b₁ b₂ (t + c)) ∘ Λ) x =
      (iteratedFDeriv ℝ j (fun t => hh b₁ b₂ (t + c)) (Λ x)).compContinuousLinearMap fun _ => Λ :=
    Λ.iteratedFDeriv_comp_right (hc c) x (by exact_mod_cast le_top)
  have e3 : ‖iteratedFDeriv ℝ j (fun t => hh b₁ b₂ (t + c)) (Λ x)‖ ≤ C := by
    rw [iteratedFDeriv_comp_add_right]; exact hC _
  have e4 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ j (fun t => hh b₁ b₂ (t + c)) (Λ x)) (fun _ : Fin j => Λ)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at e4
  have : (fun x => ((hh b₁ b₂ (Λ x + c) : ℝ) : ℂ)) =
      Complex.ofRealCLM ∘ ((fun t => hh b₁ b₂ (t + c)) ∘ Λ) := rfl
  rw [this]
  refine e1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [e2]
  exact e4.trans (mul_le_mul_of_nonneg_right e3 (pow_nonneg (norm_nonneg _) _))

end HBoundAux

namespace HBoundAux

open MasulloGRH

lemma weighted_mul_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U G : E → ℂ}
    (hU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U) (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) (Cu : ℕ → ℝ) (hCu0 : ∀ l, 0 ≤ Cu l)
    (hCu : ∀ l x, ‖iteratedFDeriv ℝ l U x‖ ≤ Cu l) (w : ℝ) (hw : 0 ≤ w) (k : ℕ) (x : E) (M : ℝ)
    (hM : ∀ l ≤ k, w * ‖iteratedFDeriv ℝ (k - l) G x‖ ≤ M) :
    w * ‖iteratedFDeriv ℝ k (fun y => U y * G y) x‖ ≤
      (∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * Cu l) * M := by
  have h1 := norm_iteratedFDeriv_mul_le hU hG x (n := k)
    (WithTop.coe_le_coe.2 (by exact_mod_cast le_top))
  calc w * ‖iteratedFDeriv ℝ k (fun y => U y * G y) x‖
      ≤ w * ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * ‖iteratedFDeriv ℝ l U x‖ *
          ‖iteratedFDeriv ℝ (k - l) G x‖ := mul_le_mul_of_nonneg_left h1 hw
    _ = ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * ‖iteratedFDeriv ℝ l U x‖ *
          (w * ‖iteratedFDeriv ℝ (k - l) G x‖) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => by ring
    _ ≤ ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * Cu l * M := by
        refine Finset.sum_le_sum fun l hl => ?_
        have hlk : l ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
        have hc : (0 : ℝ) ≤ k.choose l := Nat.cast_nonneg _
        have hM0 : 0 ≤ M := (mul_nonneg hw (norm_nonneg _)).trans (hM l hlk)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hCu l x) hc) (hM l hlk)
          (mul_nonneg hw (norm_nonneg _)) (mul_nonneg hc (hCu0 l))
    _ = _ := by rw [Finset.sum_mul]


variable {m n r s : ℕ} {d : Fin s → ℕ}

/-- the multiplier on the elementary group -/
noncomputable def vmul (b₁ b₂ : ℝ) (L : (Fin m → ℝ) →L[ℝ] ℝ) (N : (Fin r → ℤ) → ℝ)
    (e : ElemGroup m n r s d) : ℂ := ((hh b₁ b₂ (L e.1 + N e.2.2.1) : ℝ) : ℂ)

lemma vmul_key (b₁ b₂ : ℝ) (hb₁ : b₁ ≤ 0) (hb₂ : 0 ≤ b₂) (L : (Fin m → ℝ) →L[ℝ] ℝ)
    (N : (Fin r → ℤ) → ℝ) (i j k : ℕ) :
    ∃ C : ℝ, ∀ (f : ElemGroup m n r s d → ℂ),
      (∀ a b, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (elemLift f a b)) →
      ∀ M : ℝ, (∀ l ≤ k, ∀ a b xt, ‖a‖ ^ j * ‖xt.1‖ ^ i *
          ‖iteratedFDeriv ℝ (k - l) (elemLift f a b) xt‖ ≤ M) →
        ∀ a b xt, ‖a‖ ^ j * ‖xt.1‖ ^ i *
          ‖iteratedFDeriv ℝ k (elemLift (fun e => vmul b₁ b₂ L N e * f e) a b) xt‖ ≤ C * M := by
  let Λ : (Fin m → ℝ) × (Fin n → ℝ) →L[ℝ] ℝ := L.comp (ContinuousLinearMap.fst ℝ _ _)
  obtain ⟨hcd, hbd⟩ := mult_bdd b₁ b₂ hb₁ hb₂ Λ
  choose Cu hCu0 hCu using hbd
  refine ⟨∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * Cu l, fun f hf M hM a b xt => ?_⟩
  have he : elemLift (fun e => vmul b₁ b₂ L N e * f e) a b =
      fun y => ((hh b₁ b₂ (Λ y + N a) : ℝ) : ℂ) * elemLift f a b y := rfl
  rw [he]
  exact weighted_mul_bound ((hcd (N a)).of_le le_top) (hf a b) Cu hCu0 (fun l x => hCu l (N a) x) _
    (by positivity) k xt M (fun l hl => hM l hl a b xt)

theorem elem_mult (b₁ b₂ : ℝ) (hb₁ : b₁ ≤ 0) (hb₂ : 0 ≤ b₂) (L : (Fin m → ℝ) →L[ℝ] ℝ)
    (N : (Fin r → ℤ) → ℝ) :
    ∃ T : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m n r s d, Continuous T ∧
      ∀ g e, (T g).toFun e = vmul b₁ b₂ L N e * g.toFun e := by
  have hrap : ∀ g : ElemSchwartz m n r s d,
      IsRapidDecay (fun e => vmul b₁ b₂ L N e * g.toFun e) := by
    intro g
    have hg := isRapidDecay_elemSchwartz_toFun g
    let Λ : (Fin m → ℝ) × (Fin n → ℝ) →L[ℝ] ℝ := L.comp (ContinuousLinearMap.fst ℝ _ _)
    obtain ⟨hcd, -⟩ := mult_bdd b₁ b₂ hb₁ hb₂ Λ
    refine ⟨fun a b => ((hcd (N a)).of_le le_top).mul (hg.1 a b), fun i j k => ?_⟩
    obtain ⟨C, hC⟩ := vmul_key (s := s) (d := d) (n := n) b₁ b₂ hb₁ hb₂ L N i j k
    choose Cg hCg using hg.2
    let M : ℝ := ∑ l ∈ Finset.range (k + 1), max (Cg i j (k - l)) 0
    refine ⟨C * M, fun a b xt => hC g.toFun hg.1 M (fun l hl a b xt => ?_) a b xt⟩
    have hl' : l ∈ Finset.range (k + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hl)
    exact (hCg i j (k - l) a b xt).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (f := fun l => max (Cg i j (k - l)) 0)
        (fun l _ => le_max_right _ _) hl'))
  let T : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m n r s d :=
    { toFun := fun g => ⟨fun e => vmul b₁ b₂ L N e * g.toFun e, Submodule.subset_span (hrap g)⟩
      map_add' := fun g₁ g₂ => by
        apply Subtype.ext; funext e
        show vmul b₁ b₂ L N e * (g₁.toFun e + g₂.toFun e) = _ + _
        ring
      map_smul' := fun c g => by
        apply Subtype.ext; funext e
        show vmul b₁ b₂ L N e * (c * g.toFun e) = c * (vmul b₁ b₂ L N e * g.toFun e)
        ring }
  refine ⟨T, ?_, fun g e => rfl⟩
  have := elemSchwartz_continuous_of_seminorm_bound T.toAddMonoidHom (fun p => ?_)
  · exact this
  obtain ⟨i, j, k⟩ := p
  obtain ⟨C, hC⟩ := vmul_key (s := s) (d := d) (n := n) b₁ b₂ hb₁ hb₂ L N i j k
  refine ⟨(Finset.range (k + 1)).image (fun l => (i, j, k - l)), C, fun g M hM a b xt => ?_⟩
  exact hC g.toFun (isRapidDecay_elemSchwartz_toFun g).1 M (fun l hl a b xt =>
    hM (i, j, k - l) (Finset.mem_image.2 ⟨l, Finset.mem_range.2 (Nat.lt_succ_of_le hl), rfl⟩) a b xt)
    a b xt

end HBoundAux




namespace FactorAux

open MasulloGRH Topology

/-- a continuous additive map to `ℝ` vanishes at `y` if all multiples of `y` stay in a compact set -/
lemma add_zero_of_compact {A : Type*} [AddCommGroup A] [TopologicalSpace A] (f : A →+ ℝ)
    (hf : Continuous f) (K : Set A) (hK : IsCompact K) (y : A) (hy : ∀ n : ℕ, n • y ∈ K) :
    f y = 0 := by
  obtain ⟨C, hC⟩ := (hK.image hf).isBounded.subset_closedBall 0
  by_contra h
  have hpos : 0 < |f y| := abs_pos.2 h
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |f y|)
  have := hC ⟨_, hy n, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, map_nsmul, nsmul_eq_mul, Real.norm_eq_abs,
    abs_mul, Nat.abs_cast] at this
  rw [div_lt_iff₀ hpos] at hn
  linarith

variable {m n r s : ℕ} {d : Fin s → ℕ}

/-- continuous additive maps on an elementary group: `χ(x,z,a,b) = L x + N a` -/
lemma elem_char (χ : ElemGroup m n r s d →+ ℝ) (hχ : Continuous χ) (hd : ∀ i, d i ≠ 0) :
    ∃ (L : (Fin m → ℝ) →L[ℝ] ℝ) (N : (Fin r → ℤ) → ℝ),
      ∀ e : ElemGroup m n r s d, χ e = L e.1 + N e.2.2.1 := by
  let iR : (Fin m → ℝ) →+ ElemGroup m n r s d := AddMonoidHom.inl _ _
  let iT : (Fin n → UnitAddCircle) →+ ElemGroup m n r s d :=
    (AddMonoidHom.inr _ _).comp (AddMonoidHom.inl _ _)
  let iZ : (Fin r → ℤ) →+ ElemGroup m n r s d :=
    (AddMonoidHom.inr _ _).comp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inl _ _))
  let iF : ((i : Fin s) → ZMod (d i)) →+ ElemGroup m n r s d :=
    (AddMonoidHom.inr _ _).comp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inr _ _))
  have hR : Continuous (χ.comp iR) := hχ.comp (by
    show Continuous fun x : Fin m → ℝ => ((x, 0, 0, 0) : ElemGroup m n r s d); fun_prop)
  have hT : Continuous (χ.comp iT) := hχ.comp (by
    show Continuous fun z : Fin n → UnitAddCircle => ((0, z, 0, 0) : ElemGroup m n r s d); fun_prop)
  have hFc : Continuous (χ.comp iF) := hχ.comp (by
    show Continuous fun b : (i : Fin s) → ZMod (d i) => ((0, 0, 0, b) : ElemGroup m n r s d)
    fun_prop)
  have hT0 : ∀ z, χ (iT z) = 0 := fun z =>
    add_zero_of_compact (χ.comp iT) hT Set.univ isCompact_univ z (fun _ => trivial)
  haveI : ∀ i, NeZero (d i) := fun i => ⟨hd i⟩
  have hF0 : ∀ b, χ (iF b) = 0 := fun b =>
    add_zero_of_compact (χ.comp iF) hFc Set.univ isCompact_univ b (fun _ => trivial)
  refine ⟨(χ.comp iR).toRealLinearMap hR, fun a => χ (iZ a), fun e => ?_⟩
  obtain ⟨x, z, a, b⟩ := e
  have : ((x, z, a, b) : ElemGroup m n r s d) = iR x + iT z + iZ a + iF b := by
    simp [iR, iT, iZ, iF]
  have h2 : χ ((x, z, a, b) : ElemGroup m n r s d) = χ (iR x) + χ (iZ a) := by
    rw [this, map_add, map_add, map_add, hT0, hF0, add_zero, add_zero]
  rw [h2]
  rfl

lemma stage_factor {H : Type u} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H] (μ : H → ℝ) (hμc : Continuous μ) (hμp : ∀ x, 0 < μ x)
    (hμm : ∀ x y, μ (x * y) = μ x * μ y) (Γ k₁ : Subgroup H)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k₁)
    (hπ : IsElemPresentation Γ k₁ π) :
    ∃ (L : (Fin m → ℝ) →L[ℝ] ℝ) (N : (Fin r → ℤ) → ℝ), ∀ x : Γ,
      Real.log (μ x) = L (Multiplicative.toAdd (π x)).1 + N (Multiplicative.toAdd (π x)).2.2.1 := by
  classical
  let ℓ : Additive Γ →+ ℝ :=
    { toFun := fun x => Real.log (μ (Additive.toMul x : Γ))
      map_zero' := by
        show Real.log (μ ((1 : Γ) : H)) = 0
        have h := hμm 1 1
        rw [mul_one] at h
        have hp := hμp 1
        have : μ 1 = 1 := by nlinarith
        simp [this]
      map_add' := fun x y => by
        show Real.log (μ ((Additive.toMul x * Additive.toMul y : Γ) : H)) = _
        rw [Subgroup.coe_mul, hμm, Real.log_mul (hμp _).ne' (hμp _).ne']
        all_goals rfl }
  have hℓc : Continuous fun x : Γ => ℓ (Additive.ofMul x) :=
    (hμc.comp continuous_subtype_val).log fun x => (hμp _).ne'
  -- `ℓ` kills `k₁`
  have hK : IsCompact {y : Γ | (y : H) ∈ k₁} := by
    rw [Subtype.isCompact_iff]
    have : ((↑) : Γ → H) '' {y : Γ | (y : H) ∈ k₁} = (k₁ : Set H) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, hs.2.2.2 hx⟩, hx, rfl⟩
    rw [this]; exact isCompact_of_isGoodSubgroup H k₁ hs.2.2.1
  have hker : ∀ y : Γ, (y : H) ∈ k₁ → ℓ (Additive.ofMul y) = 0 := by
    intro y hy
    refine add_zero_of_compact ℓ ?_ (Additive.toMul ⁻¹' {y : Γ | (y : H) ∈ k₁}) ?_
      (Additive.ofMul y) fun j => ?_
    · exact hℓc
    · exact hK
    · show ((y ^ j : Γ) : H) ∈ k₁
      rw [Subgroup.coe_pow]; exact k₁.pow_mem hy j
  have hℓeq : ∀ x y : Γ, π x = π y → ℓ (Additive.ofMul x) = ℓ (Additive.ofMul y) := by
    intro x y hxy
    have h1 : π (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 := hker _ ((hπ.2.2.2.2 _).1 h1)
    have h3 : Additive.ofMul x = Additive.ofMul (x * y⁻¹) + Additive.ofMul y := by
      show x = x * y⁻¹ * y; group
    rw [h3, map_add, h2, zero_add]
  choose pre hpre using fun e : ElemGroup m n r s d => hπ.2.2.2.1 (Multiplicative.ofAdd e)
  let χf : ElemGroup m n r s d → ℝ := fun e => ℓ (Additive.ofMul (pre e))
  have hχπ : ∀ x : Γ, χf (Multiplicative.toAdd (π x)) = ℓ (Additive.ofMul x) := fun x =>
    hℓeq _ _ (by rw [hpre]; rfl)
  let χ : ElemGroup m n r s d →+ ℝ :=
    { toFun := χf
      map_zero' := by
        have := hχπ 1
        rw [map_one] at this
        rw [show (0 : ElemGroup m n r s d) = Multiplicative.toAdd 1 from rfl, this]
        exact ℓ.map_zero
      map_add' := fun e₁ e₂ => by
        have h₁ := hχπ (pre e₁)
        have h₂ := hχπ (pre e₂)
        have h₁₂ := hχπ (pre e₁ * pre e₂)
        rw [hpre] at h₁ h₂
        rw [map_mul, hpre, hpre] at h₁₂
        rw [show e₁ + e₂ = Multiplicative.toAdd (Multiplicative.ofAdd e₁ * Multiplicative.ofAdd e₂)
          from rfl, h₁₂, show Additive.ofMul (pre e₁ * pre e₂) =
            Additive.ofMul (pre e₁) + Additive.ofMul (pre e₂) from rfl, map_add]
        all_goals rfl }
  have hq : IsQuotientMap fun x : Γ => Multiplicative.toAdd (π x) :=
    IsOpenMap.isQuotientMap hπ.2.2.1 hπ.2.1 (fun e => ⟨pre e, hpre e⟩)
  have hχc : Continuous χ := by
    refine hq.continuous_iff.2 ?_
    have : (χ ∘ fun x : Γ => Multiplicative.toAdd (π x)) = fun x : Γ => ℓ (Additive.ofMul x) :=
      funext hχπ
    rw [this]; exact hℓc
  obtain ⟨L, N, hLN⟩ := elem_char χ hχc hπ.1
  refine ⟨L, N, fun x => ?_⟩
  rw [← hLN]
  exact (hχπ x).symm

end FactorAux

namespace PullbackAux

open MasulloGRH

lemma ws_all {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] {ι : Type*} {p : SeminormFamily ℂ E ι} (hp : WithSeminorms p) :
    WithSeminorms (fun q : {q : Seminorm ℂ E // Continuous q} => q.1) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
  refine le_antisymm (le_iInf fun q => ?_) ?_
  · rw [← Filter.tendsto_iff_comap]
    have := q.2.tendsto 0
    rwa [map_zero] at this
  · rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf p).1 hp]
    exact le_iInf fun i => iInf_le_of_le ⟨p i, hp.continuous_seminorm i⟩ le_rfl

/-- a `WithSeminorms` topology, with any index, is locally convex -/
lemma lc_of_ws {E : Type u} [AddCommGroup E] [Module ℂ E] (t : TopologicalSpace E)
    {ι : Type*} {p : SeminormFamily ℂ E ι} (hp : @WithSeminorms ℂ E ι _ _ _ p t) :
    IsLocallyConvexTopology E t := by
  letI := t
  haveI : IsTopologicalAddGroup E := hp.topologicalAddGroup
  exact ⟨{q : Seminorm ℂ E // Continuous q}, ⟨⟨0, continuous_const⟩⟩, _, ws_all hp⟩

/-- an infimum of locally convex topologies is locally convex -/
lemma lc_sInf {E : Type u} [AddCommGroup E] [Module ℂ E] (S : Set (TopologicalSpace E))
    (hS : ∀ t ∈ S, IsLocallyConvexTopology E t) : IsLocallyConvexTopology E (sInf S) := by
  choose ι _ p hp using fun t : S => hS t.1 t.2
  rw [sInf_eq_iInf']
  exact lc_of_ws _ (withSeminorms_iInf (p := p) (t := fun t : S => t.1) hp)

variable {H : Type u} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- the topology of `S(H)` is locally convex -/
lemma sb_lc : IsLocallyConvexTopology (SchwartzBruhat H) inferInstance :=
  lc_sInf _ fun _ ht => ht.1

/-- universal property of the inductive limit topology of `S(H)` -/
lemma sb_continuous_of_ofElem {X : Type u} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (hX : IsLocallyConvexTopology X inferInstance) (Q : SchwartzBruhat H →ₗ[ℂ] X)
    (hQ : ∀ (Γ k : Subgroup H) (m n r s : ℕ) (d : Fin s → ℕ)
      (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
      (hπ : IsElemPresentation Γ k π), Continuous (fun g => Q (SchwartzBruhat.ofElem Γ k π hs hπ g))) :
    Continuous Q := by
  obtain ⟨ι, hι, p, hp⟩ := hX
  rw [continuous_iff_le_induced]
  refine sInf_le ⟨lc_of_ws _ (LinearMap.withSeminorms_induced hp Q), fun Γ k m n r s d π hs hπ => ?_⟩
  exact continuous_induced_rng.2 (hQ Γ k m n r s d π hs hπ)

lemma ofElem_continuous {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup H)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : Continuous (SchwartzBruhat.ofElem Γ k π hs hπ) :=
  continuous_sInf_rng.2 fun _ ht => ht.2 Γ k m n r s d π hs hπ

end PullbackAux

open MasulloGRH PullbackAux HBoundAux FactorAux in
theorem solution
    (H : Type u) [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [LocallyCompactSpace H] [SecondCountableTopology H] (μ : H → ℝ) (hμc : Continuous μ)
    (hμp : ∀ x, 0 < μ x) (hμm : ∀ x y, μ (x * y) = μ x * μ y) (b₁ b₂ : ℝ)
    (hb₁ : b₁ ≤ 0) (hb₂ : 0 ≤ b₂) :
    ∃ M : SchwartzBruhat H →L[ℂ] SchwartzBruhat H, ∀ (f : SchwartzBruhat H) (x : H),
      (M f).toFun x = ((μ x ^ b₁ + μ x ^ b₂ : ℝ)⁻¹ : ℂ) * f.toFun x := by
  classical
  let w : H → ℂ := fun x => ((μ x ^ b₁ + μ x ^ b₂ : ℝ)⁻¹ : ℂ)
  -- the stage computation
  have hstage : ∀ (Γ k₁ : Subgroup H) (m n r s : ℕ) (d : Fin s → ℕ)
      (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k₁)
      (hπ : IsElemPresentation Γ k₁ π),
      ∃ T : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m n r s d, Continuous T ∧
        ∀ g : ElemSchwartz m n r s d,
          (fun x => w x * extendPullback Γ π g.toFun x) = extendPullback Γ π (T g).toFun := by
    intro Γ k₁ m n r s d π hs hπ
    obtain ⟨L, N, hLN⟩ := stage_factor μ hμc hμp hμm Γ k₁ π hs hπ
    obtain ⟨T, hTc, hT⟩ := elem_mult (n := n) (s := s) (d := d) b₁ b₂ hb₁ hb₂ L N
    refine ⟨T, hTc, fun g => ?_⟩
    funext x
    unfold extendPullback
    by_cases hx : x ∈ Γ
    · rw [dif_pos hx, dif_pos hx, hT]
      congr 1
      unfold vmul hh
      rw [← hLN ⟨x, hx⟩]
      show ((μ x ^ b₁ + μ x ^ b₂ : ℝ)⁻¹ : ℂ) = _
      rw [Real.rpow_def_of_pos (hμp x), Real.rpow_def_of_pos (hμp x), mul_comm (Real.log (μ x)) b₁,
        mul_comm (Real.log (μ x)) b₂]
      first | rfl | (push_cast; rfl) | simp
    · rw [dif_neg hx, dif_neg hx, mul_zero]
  have hmem : ∀ f ∈ schwartzBruhatSubmodule H, (fun x => w x * f x) ∈ schwartzBruhatSubmodule H := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨Γ, k₁, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hf
      obtain ⟨T, -, hT⟩ := hstage Γ k₁ m n r s d π hs hπ
      rw [hT g]
      exact Submodule.subset_span ⟨Γ, k₁, m, n, r, s, d, π, T g, hs, hπ, rfl⟩
    | zero =>
      have : (fun x => w x * (0 : H → ℂ) x) = 0 := by funext x; simp
      rw [this]; exact Submodule.zero_mem _
    | add f₁ f₂ _ _ h₁ h₂ =>
      have : (fun x => w x * (f₁ + f₂) x) = (fun x => w x * f₁ x) + (fun x => w x * f₂ x) := by
        funext x; simp [mul_add]
      rw [this]; exact Submodule.add_mem _ h₁ h₂
    | smul c f _ h =>
      have : (fun x => w x * (c • f) x) = c • (fun x => w x * f x) := by
        funext x; simp; ring
      rw [this]; exact Submodule.smul_mem _ c h
  let Mₗ : SchwartzBruhat H →ₗ[ℂ] SchwartzBruhat H :=
    { toFun := fun f => ⟨fun x => w x * f.1 x, hmem f.1 f.2⟩
      map_add' := fun f₁ f₂ => by
        apply Subtype.ext; funext x
        show w x * (f₁.1 x + f₂.1 x) = w x * f₁.1 x + w x * f₂.1 x
        ring
      map_smul' := fun c f => by
        apply Subtype.ext; funext x
        show w x * (c * f.1 x) = c * (w x * f.1 x)
        ring }
  have hM : Continuous Mₗ := by
    refine sb_continuous_of_ofElem sb_lc Mₗ fun Γ k₁ m n r s d π hs hπ => ?_
    obtain ⟨T, hTc, hT⟩ := hstage Γ k₁ m n r s d π hs hπ
    have : (fun g => Mₗ (SchwartzBruhat.ofElem Γ k₁ π hs hπ g)) =
        SchwartzBruhat.ofElem Γ k₁ π hs hπ ∘ T := by
      funext g
      apply Subtype.ext
      exact hT g
    rw [this]
    exact (ofElem_continuous _ _ _ _ _).comp hTc
  exact ⟨⟨Mₗ, hM⟩, fun f x => rfl⟩
