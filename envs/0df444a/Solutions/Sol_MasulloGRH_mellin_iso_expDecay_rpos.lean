-- Prove2me | solution 1 for MasulloGRH.mellin_iso_expDecay_rpos
-- status  : ACCEPTED   (prove)
-- author  : @Miikka
-- created : 2026-11-21T06:49:01.941198+00:00
-- url     : https://prove2.me/submissions/4a3184e5-bfec-45d9-9a5c-61fcce62e932

import Definitions.Def_MasulloGRH_ExpDecaySpaces
import Theorems.Thm_MasulloGRH_expDecaySchwartzRpos_concrete
import Theorems.Thm_MellinStrip_expDecay_strip
import Theorems.Thm_MellinStrip_line_L2_clm
import Theorems.Thm_MellinStrip_reverse_estimate
import Theorems.Thm_MellinStrip_surjective

set_option autoImplicit false

open MeasureTheory MasulloGRH

namespace MellinIsoAux

noncomputable section

variable {I : Set ℝ}

/-! ### The Schwartz–Bergman side -/

lemma ush_zero : IsUniformlySchwartzHolomorphic I 0 :=
  ⟨fun _ _ => rfl, differentiableOn_const 0, fun _ _ _ _ => ⟨0, fun s _ _ => by simp⟩⟩

lemma ush_add {f g : ℂ → ℂ} (hf : IsUniformlySchwartzHolomorphic I f)
    (hg : IsUniformlySchwartzHolomorphic I g) : IsUniformlySchwartzHolomorphic I (f + g) := by
  refine ⟨fun s hs => by simp [hf.1 s hs, hg.1 s hs], hf.2.1.add hg.2.1, fun a b hab N => ?_⟩
  obtain ⟨C1, h1⟩ := hf.2.2 a b hab N
  obtain ⟨C2, h2⟩ := hg.2.2 a b hab N
  refine ⟨C1 + C2, fun s ha hb => ?_⟩
  have := norm_add_le (s ^ N * f s) (s ^ N * g s)
  rw [← mul_add] at this
  simp only [Pi.add_apply]
  linarith [h1 s ha hb, h2 s ha hb]

lemma ush_smul (c : ℂ) {f : ℂ → ℂ} (hf : IsUniformlySchwartzHolomorphic I f) :
    IsUniformlySchwartzHolomorphic I (c • f) := by
  refine ⟨fun s hs => by simp [hf.1 s hs], hf.2.1.const_smul c, fun a b hab N => ?_⟩
  obtain ⟨C1, h1⟩ := hf.2.2 a b hab N
  refine ⟨‖c‖ * C1, fun s ha hb => ?_⟩
  have : s ^ N * (c • f) s = c * (s ^ N * f s) := by
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [this, norm_mul]
  exact mul_le_mul_of_nonneg_left (h1 s ha hb) (norm_nonneg c)

lemma ush_of_mem {f : ℂ → ℂ} (hf : f ∈ schwartzBergmanSubmodule I) :
    IsUniformlySchwartzHolomorphic I f := by
  unfold schwartzBergmanSubmodule at hf
  induction hf using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ush_zero
  | add x y _ _ hx hy => exact ush_add hx hy
  | smul c x _ hx => exact ush_smul c hx

lemma re_line (a y : ℝ) : ((a : ℂ) + y * Complex.I).re = a := by simp

lemma memLp_line (hI : IsOpen I) {f : ℂ → ℂ} (hf : IsUniformlySchwartzHolomorphic I f) {a : ℝ}
    (ha : a ∈ I) (N : ℕ) :
    MemLp (fun x : ℝ => ((a : ℂ) + x * Complex.I) ^ N * f (a + x * Complex.I)) 2 volume := by
  have hopen : IsOpen {s : ℂ | s.re ∈ I} := hI.preimage Complex.continuous_re
  have hl : Continuous (fun x : ℝ => (a : ℂ) + x * Complex.I) := by fun_prop
  have hcont : Continuous (fun x : ℝ => ((a : ℂ) + x * Complex.I) ^ N * f (a + x * Complex.I)) := by
    refine (hl.pow N).mul ?_
    refine continuous_iff_continuousAt.2 fun x => ?_
    have hx : ((a : ℂ) + x * Complex.I) ∈ {s : ℂ | s.re ∈ I} := by
      simp only [Set.mem_ofPred_eq, re_line]; exact ha
    exact ContinuousAt.comp (g := f) (f := fun x : ℝ => (a : ℂ) + x * Complex.I) (x := x)
      ((hf.2.1.differentiableAt (hopen.mem_nhds hx)).continuousAt) hl.continuousAt
  have hIcc : Set.Icc a a ⊆ I := by rw [Set.Icc_self]; exact Set.singleton_subset_iff.2 ha
  obtain ⟨C0, h0⟩ := hf.2.2 a a hIcc N
  obtain ⟨C2, h2⟩ := hf.2.2 a a hIcc (N + 2)
  set h := fun x : ℝ => ((a : ℂ) + x * Complex.I) ^ N * f (a + x * Complex.I) with hh
  have hb : ∀ x : ℝ, ‖h x‖ * (1 + x ^ 2) ≤ C0 + C2 := by
    intro x
    have e0 := h0 ((a : ℂ) + x * Complex.I) (by rw [re_line]) (by rw [re_line])
    have e2 := h2 ((a : ℂ) + x * Complex.I) (by rw [re_line]) (by rw [re_line])
    have hn : ‖(a : ℂ) + x * Complex.I‖ ^ 2 = a ^ 2 + x ^ 2 := by
      rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
    have : ‖((a : ℂ) + x * Complex.I) ^ (N + 2) * f (a + x * Complex.I)‖ =
        ‖(a : ℂ) + x * Complex.I‖ ^ 2 * ‖h x‖ := by
      rw [hh]; simp only [norm_mul, norm_pow]; ring
    rw [this, hn] at e2
    have hx0 : 0 ≤ ‖h x‖ := norm_nonneg _
    nlinarith [sq_nonneg a]
  set Cb := C0 + C2
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (Cb ^ 2))
    (hcont.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have h1 := hb x
  have e1 : ‖h x‖ ≤ Cb / (1 + x ^ 2) := (le_div_iff₀ hpos).2 h1
  have e2 : ‖h x‖ ≤ Cb :=
    le_trans (le_mul_of_one_le_right (norm_nonneg _) (by nlinarith)) h1
  rw [Real.norm_of_nonneg (by positivity)]
  calc ‖h x‖ ^ 2 = ‖h x‖ * ‖h x‖ := sq _
    _ ≤ Cb * (Cb / (1 + x ^ 2)) := mul_le_mul e2 e1 (norm_nonneg _) (le_trans (norm_nonneg _) e2)
    _ = Cb ^ 2 * (1 + x ^ 2)⁻¹ := by ring

lemma ush_toFun (F : SchwartzBergman I) : IsUniformlySchwartzHolomorphic I F.toFun :=
  ush_of_mem F.2

lemma lineL2_eq (hI : IsOpen I) (F : SchwartzBergman I) {a : ℝ} (ha : a ∈ I) (N : ℕ) :
    F.lineL2 a N = (memLp_line hI (ush_toFun F) ha N).toLp _ := by
  unfold SchwartzBergman.lineL2
  rw [dif_pos (memLp_line hI (ush_toFun F) ha N)]

lemma toFun_add_SB (F G : SchwartzBergman I) : (F + G).toFun = F.toFun + G.toFun := rfl
lemma toFun_smul_SB (c : ℂ) (F : SchwartzBergman I) : (c • F).toFun = c • F.toFun := rfl

/-- The line seminorm map as a linear map. -/
noncomputable def lineLin (hI : IsOpen I) (a : ℝ) (ha : a ∈ I) (N : ℕ) :
    SchwartzBergman I →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun F := F.lineL2 a N
  map_add' F G := by
    rw [lineL2_eq hI F ha, lineL2_eq hI G ha, lineL2_eq hI (F + G) ha, ← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
    simp only [toFun_add_SB, Pi.add_apply, mul_add]
  map_smul' c F := by
    rw [lineL2_eq hI F ha, lineL2_eq hI (c • F) ha, RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
    simp only [toFun_smul_SB, Pi.smul_apply, smul_eq_mul]; ring

lemma tag (hI : IsOpen I) : IsTopologicalAddGroup (SchwartzBergman I) := by
  have : ∀ (a : ℝ) (ha : a ∈ I) (N : ℕ), @IsTopologicalAddGroup (SchwartzBergman I)
      (TopologicalSpace.induced (fun ϕ : SchwartzBergman I => ϕ.lineL2 a N) inferInstance) _ :=
    fun a ha N => topologicalAddGroup_induced (lineLin hI a ha N)
  exact topologicalAddGroup_iInf fun a => topologicalAddGroup_iInf fun ha =>
    topologicalAddGroup_iInf fun N => this a ha N

lemma continuous_lineL2 (a : ℝ) (ha : a ∈ I) (N : ℕ) :
    Continuous (fun F : SchwartzBergman I => F.lineL2 a N) := by
  apply continuous_iInf_dom (i := a)
  apply continuous_iInf_dom (i := ha)
  apply continuous_iInf_dom (i := N)
  exact continuous_induced_dom

/-! ### The exponential-decay side -/

lemma toFun_add_ED (ϕ χ : ExpDecaySchwartzRpos I) : (ϕ + χ).toFun = ϕ.toFun + χ.toFun := rfl
lemma toFun_smul_ED (c : ℂ) (ϕ : ExpDecaySchwartzRpos I) : (c • ϕ).toFun = c • ϕ.toFun := rfl
lemma toFun_sub_ED (ϕ χ : ExpDecaySchwartzRpos I) : (ϕ - χ).toFun = ϕ.toFun - χ.toFun := rfl

/-- Abbreviation for the hypothesis supplied by the concrete description of `S_I(ℝ_{>0})`. -/
def ConcreteMem (I : Set ℝ) : Prop :=
  ∀ f : Multiplicative ℝ → ℂ, f ∈ expDecaySubmodule (Multiplicative ℝ) rposModule I ↔
    ∀ a ∈ I, ∃ g : SchwartzMap ℝ ℂ, ∀ x : ℝ,
      g x = (Real.exp (a * x) : ℂ) * f (Multiplicative.ofAdd x)

/-- `ψ(x) = ϕ(e^x)`. -/
def psi (ϕ : ExpDecaySchwartzRpos I) : ℝ → ℂ := fun x => ϕ.toFun (Multiplicative.ofAdd x)

lemma hpsi (hA : ConcreteMem I) (ϕ : ExpDecaySchwartzRpos I) :
    ∀ a ∈ I, ∃ g : SchwartzMap ℝ ℂ, ∀ x : ℝ, g x = (Real.exp (a * x) : ℂ) * psi ϕ x :=
  (hA ϕ.1).1 ϕ.2

open Classical in
noncomputable def wt (hA : ConcreteMem I) (a : ℝ) (ϕ : ExpDecaySchwartzRpos I) :
    SchwartzMap ℝ ℂ :=
  if h : a ∈ I then (hpsi hA ϕ a h).choose else 0

lemma wt_apply (hA : ConcreteMem I) (a : ℝ) (ha : a ∈ I) (ϕ : ExpDecaySchwartzRpos I) (x : ℝ) :
    wt hA a ϕ x = (Real.exp (a * x) : ℂ) * ϕ.toFun (Multiplicative.ofAdd x) := by
  unfold wt
  rw [dif_pos ha]
  exact (hpsi hA ϕ a ha).choose_spec x

noncomputable def wtLin (hA : ConcreteMem I) (a : ℝ) (ha : a ∈ I) :
    ExpDecaySchwartzRpos I →ₗ[ℂ] SchwartzMap ℝ ℂ where
  toFun := wt hA a
  map_add' ϕ χ := by
    ext x
    simp only [add_apply, wt_apply hA a ha, toFun_add_ED, Pi.add_apply, mul_add]
  map_smul' c ϕ := by
    ext x
    simp only [smul_apply, wt_apply hA a ha, toFun_smul_ED, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

lemma integrand_eq (a y x : ℝ) (c : ℂ) :
    ((Real.exp (a * x) : ℂ) * c) * Complex.exp (y * Complex.I * x) =
      c * Complex.exp (((a : ℂ) + y * Complex.I) * x) := by
  rw [Complex.ofReal_exp,
    show ((a : ℂ) + y * Complex.I) * x = ((a * x : ℝ) : ℂ) + y * Complex.I * x by push_cast; ring,
    Complex.exp_add]
  ring

/-! ### The Mellin map -/

open Classical in
noncomputable def Mfun (ϕ : ExpDecaySchwartzRpos I) : ℂ → ℂ :=
  fun s => if s.re ∈ I then ϕ.mellin s else 0

lemma mellin_eq (ϕ : ExpDecaySchwartzRpos I) (s : ℂ) :
    ϕ.mellin s = ∫ x : ℝ, psi ϕ x * Complex.exp (s * x) := rfl

lemma ush_M (hI : IsOpen I) (hA : ConcreteMem I) (ϕ : ExpDecaySchwartzRpos I) :
    IsUniformlySchwartzHolomorphic I (Mfun ϕ) := by
  obtain ⟨_, hd, hb⟩ := MellinStrip.expDecay_strip I hI (psi ϕ) (hpsi hA ϕ)
  refine ⟨fun s hs => by simp [Mfun, hs], hd.congr fun s hs => ?_, fun a b hab N => ?_⟩
  · simp only [Mfun, if_pos (show s.re ∈ I from hs)]; rfl
  · obtain ⟨C, hC⟩ := hb a b hab N
    refine ⟨C, fun s ha hb' => ?_⟩
    have hs : s.re ∈ I := hab ⟨ha, hb'⟩
    simp only [Mfun, if_pos hs]
    exact hC s ha hb'

lemma mfun_mem (hI : IsOpen I) (hA : ConcreteMem I) (ϕ : ExpDecaySchwartzRpos I) :
    Mfun ϕ ∈ schwartzBergmanSubmodule I := by
  unfold schwartzBergmanSubmodule
  exact Submodule.subset_span (ush_M hI hA ϕ)

lemma integrable_psi (hI : IsOpen I) (hA : ConcreteMem I) (ϕ : ExpDecaySchwartzRpos I) (s : ℂ)
    (hs : s.re ∈ I) : Integrable (fun x : ℝ => psi ϕ x * Complex.exp (s * x)) :=
  (MellinStrip.expDecay_strip I hI (psi ϕ) (hpsi hA ϕ)).1 s hs

noncomputable def Mlin (hI : IsOpen I) (hA : ConcreteMem I) :
    ExpDecaySchwartzRpos I →ₗ[ℂ] SchwartzBergman I where
  toFun ϕ := (⟨Mfun ϕ, mfun_mem hI hA ϕ⟩ : ↥(schwartzBergmanSubmodule I))
  map_add' ϕ χ := by
    apply Subtype.ext
    funext s
    change Mfun (ϕ + χ) s = Mfun ϕ s + Mfun χ s
    by_cases hs : s.re ∈ I
    · simp only [Mfun, if_pos hs, mellin_eq]
      rw [← integral_add (integrable_psi hI hA ϕ s hs) (integrable_psi hI hA χ s hs)]
      congr 1
      funext x
      simp only [psi, toFun_add_ED, Pi.add_apply, add_mul]
    · simp [Mfun, hs]
  map_smul' c ϕ := by
    apply Subtype.ext
    funext s
    change Mfun (c • ϕ) s = c * Mfun ϕ s
    by_cases hs : s.re ∈ I
    · simp only [Mfun, if_pos hs, mellin_eq]
      rw [← integral_const_mul]
      congr 1
      funext x
      simp only [psi, toFun_smul_ED, Pi.smul_apply, smul_eq_mul]; ring
    · simp [Mfun, hs]

lemma Mlin_toFun (hI : IsOpen I) (hA : ConcreteMem I) (ϕ : ExpDecaySchwartzRpos I) :
    (Mlin hI hA ϕ).toFun = Mfun ϕ := rfl

lemma Mlin_line (hI : IsOpen I) (hA : ConcreteMem I) (ϕ : ExpDecaySchwartzRpos I) {b : ℝ}
    (hb : b ∈ I) (y : ℝ) :
    (Mlin hI hA ϕ).toFun ((b : ℂ) + y * Complex.I) =
      ∫ x : ℝ, psi ϕ x * Complex.exp (((b : ℂ) + y * Complex.I) * x) := by
  show Mfun ϕ _ = _
  unfold Mfun
  rw [if_pos (by rw [re_line]; exact hb)]
  rfl

end

end MellinIsoAux

open MellinIsoAux

lemma sem_sum_apply {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*}
    (p : ι → Seminorm ℂ E) (S : Finset ι) (x : E) :
    (∑ i ∈ S, p i) x = ∑ i ∈ S, p i x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, add_apply, ih]

theorem solution (I : Set ℝ) (hI : IsOpen I) (hI' : I.OrdConnected)
    (hne : I.Nonempty) :
    ∃ M : ExpDecaySchwartzRpos I →ₗ[ℂ] SchwartzBergman I,
      IsLinearTopologicalIso M ∧
      ∀ (ϕ : ExpDecaySchwartzRpos I) (s : ℂ), s.re ∈ I →
        MeasureTheory.Integrable
          (fun x : ℝ => ϕ.toFun (Multiplicative.ofAdd x) * Complex.exp (s * x)) ∧
        (M ϕ).toFun s = ϕ.mellin s := by
  obtain ⟨hA, hT⟩ := expDecaySchwartzRpos_concrete I hne
  have hτ := hT (wt hA) (wt_apply hA)
  have := tag (I := I) hI
  -- injectivity
  have hinj : Function.Injective (Mlin hI hA) := by
    intro ϕ χ hϕχ
    obtain ⟨a0, ha0⟩ := hne
    obtain ⟨S, C, hS, hB⟩ := MellinStrip.reverse_estimate I hI a0 ha0 0 0
    have hMδ : Mlin hI hA (ϕ - χ) = 0 := by rw [map_sub, hϕχ, sub_self]
    have hline : ∀ p ∈ S, (fun y : ℝ => ((p.1 : ℂ) + y * Complex.I) ^ p.2 *
        ∫ x : ℝ, psi (ϕ - χ) x * Complex.exp (((p.1 : ℂ) + y * Complex.I) * x)) = 0 := by
      intro p hp
      funext y
      rw [← Mlin_line hI hA (ϕ - χ) (hS p hp) y, hMδ]
      change _ * (0 : ℂ → ℂ) _ = (0 : ℝ → ℂ) y
      simp
    have hsn := hB (psi (ϕ - χ)) (fun b => wt hA b (ϕ - χ))
      (fun b hb x => wt_apply hA b hb (ϕ - χ) x)
    rw [Finset.sum_eq_zero (fun p hp => by rw [hline p hp]; simp), mul_zero] at hsn
    have hw0 : ∀ x, wt hA a0 (ϕ - χ) x = 0 := fun x =>
      norm_le_zero_iff.1 (le_trans (SchwartzMap.norm_le_seminorm ℂ (wt hA a0 (ϕ - χ)) x) hsn)
    have hδ0 : (ϕ - χ).toFun = 0 := by
      funext y
      have := hw0 (Multiplicative.toAdd y)
      rw [wt_apply hA a0 ha0] at this
      simpa [Real.exp_ne_zero] using this
    have : ϕ - χ = 0 := Subtype.ext hδ0
    exact sub_eq_zero.1 this
  -- surjectivity
  have hsurj : Function.Surjective (Mlin hI hA) := by
    intro F
    have hF := ush_toFun F
    obtain ⟨ψ, hψ, hψM⟩ := MellinStrip.surjective I hI hI' F.toFun hF.2.1 hF.2.2
    let ϕ0 : ExpDecaySchwartzRpos I :=
      (⟨fun y => ψ (Multiplicative.toAdd y), (hA _).2 (fun a ha => hψ a ha)⟩ :
        ↥(expDecaySubmodule (Multiplicative ℝ) rposModule I))
    refine ⟨ϕ0, ?_⟩
    apply Subtype.ext
    funext s
    change Mfun ϕ0 s = F.toFun s
    by_cases hs : s.re ∈ I
    · simp only [Mfun, if_pos hs, mellin_eq]
      exact hψM s hs
    · simp only [Mfun, if_neg hs]
      exact (hF.1 s hs).symm
  have hbij : Function.Bijective (Mlin hI hA) := ⟨hinj, hsurj⟩
  -- continuity
  have hcont : Continuous (Mlin hI hA) := by
    have key : @Continuous _ _
        (⨅ (a : ℝ) (_ : a ∈ I), TopologicalSpace.induced (wt hA a) inferInstance) _
        (Mlin hI hA) := by
      refine continuous_iInf_rng.2 fun a => continuous_iInf_rng.2 fun ha =>
        continuous_iInf_rng.2 fun N => continuous_induced_rng.2 ?_
      obtain ⟨L, hL⟩ := MellinStrip.line_L2_clm a N
      have heq : (fun ϕ => (Mlin hI hA ϕ).lineL2 a N) = fun ϕ => L (wt hA a ϕ) := by
        funext ϕ
        rw [lineL2_eq hI (Mlin hI hA ϕ) ha N]
        refine Lp.ext ((MemLp.coeFn_toLp _).trans (Filter.EventuallyEq.trans ?_ (hL _).symm))
        refine Filter.Eventually.of_forall fun y => ?_
        dsimp only
        rw [Mlin_line hI hA ϕ ha y]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        rw [wt_apply hA a ha, integrand_eq]
        rfl
      rw [show ((fun ϕ : SchwartzBergman I => ϕ.lineL2 a N) ∘ ⇑(Mlin hI hA)) =
        fun ϕ => L (wt hA a ϕ) from heq]
      refine @Continuous.comp _ _ _
        (⨅ (a : ℝ) (_ : a ∈ I), TopologicalSpace.induced (wt hA a) inferInstance) _ _ _ _
        L.continuous ?_
      apply continuous_iInf_dom (i := a)
      apply continuous_iInf_dom (i := ha)
      exact continuous_induced_dom
    convert key
  -- continuity of the inverse
  let e := LinearEquiv.ofBijective (Mlin hI hA) hbij
  have hsymm : Continuous e.symm := by
    have key : @Continuous _ _ _
        (⨅ (a : ℝ) (_ : a ∈ I), TopologicalSpace.induced (wt hA a) inferInstance)
        e.symm := by
      refine continuous_iInf_rng.2 fun a => continuous_iInf_rng.2 fun ha =>
        continuous_induced_rng.2 ?_
      let T : SchwartzBergman I →ₗ[ℂ] SchwartzMap ℝ ℂ :=
        (wtLin hA a ha).comp e.symm.toLinearMap
      show Continuous T
      refine WithSeminorms.continuous_of_continuous_comp (schwartz_withSeminorms ℂ ℝ ℂ) T
        (fun i => ?_)
      obtain ⟨S, C, hS, hB⟩ := MellinStrip.reverse_estimate I hI a ha i.1 i.2
      classical
      let p' : ℝ × ℕ → Seminorm ℂ (SchwartzBergman I) := fun p =>
        if h : p.1 ∈ I then
          (normSeminorm ℂ (Lp ℂ 2 (volume : Measure ℝ))).comp (lineLin hI p.1 h p.2)
        else 0
      have hp' : ∀ p ∈ S, ∀ F, p' p F = ‖F.lineL2 p.1 p.2‖ := fun p hp F => by
        simp only [p', dif_pos (hS p hp)]
        rfl
      have hcp : ∀ p ∈ S, Continuous (p' p) := fun p hp => by
        have : (p' p : SchwartzBergman I → ℝ) = fun F => ‖F.lineL2 p.1 p.2‖ :=
          funext (hp' p hp)
        rw [this]
        exact continuous_norm.comp (continuous_lineL2 p.1 (hS p hp) p.2)
      let R : Seminorm ℂ (SchwartzBergman I) := (max C 0).toNNReal • ∑ p ∈ S, p' p
      have hRapp : ∀ F, R F = max C 0 * ∑ p ∈ S, ‖F.lineL2 p.1 p.2‖ := fun F => by
        show ((max C 0).toNNReal • ∑ p ∈ S, p' p) F = _
        rw [smul_apply, NNReal.smul_def, sem_sum_apply, smul_eq_mul,
          Real.coe_toNNReal _ (le_max_right _ _)]
        congr 1
        exact Finset.sum_congr rfl fun p hp => hp' p hp F
      have hR : Continuous R := by
        have : (R : SchwartzBergman I → ℝ) = fun F => max C 0 * ∑ p ∈ S, ‖F.lineL2 p.1 p.2‖ :=
          funext hRapp
        rw [this]
        refine continuous_const.mul (continuous_finsetSum _ fun p hp => ?_)
        exact continuous_norm.comp (continuous_lineL2 p.1 (hS p hp) p.2)
      refine Seminorm.continuous_of_le hR (fun F => ?_)
      show SchwartzMap.seminorm ℂ i.1 i.2 (wt hA a (e.symm F)) ≤ R F
      have hF : Mlin hI hA (e.symm F) = F := e.apply_symm_apply F
      have hB' := hB (psi (e.symm F)) (fun b => wt hA b (e.symm F))
        (fun b hb x => wt_apply hA b hb (e.symm F) x)
      have hterm : ∀ p ∈ S, (eLpNorm (fun y : ℝ => ((p.1 : ℂ) + y * Complex.I) ^ p.2 *
          ∫ x : ℝ, psi (e.symm F) x * Complex.exp (((p.1 : ℂ) + y * Complex.I) * x))
            2 volume).toReal = ‖F.lineL2 p.1 p.2‖ := by
        intro p hp
        rw [lineL2_eq hI F (hS p hp), Lp.norm_toLp]
        have hF' : F.toFun = (Mlin hI hA (e.symm F)).toFun := by rw [hF]
        refine congrArg ENNReal.toReal
          (congrArg (fun f => eLpNorm f 2 volume) (funext fun y => ?_))
        rw [hF', Mlin_line hI hA _ (hS p hp) y]
      rw [Finset.sum_congr rfl hterm] at hB'
      rw [hRapp]
      refine le_trans hB' (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
      exact Finset.sum_nonneg fun p _ => norm_nonneg _
    convert key
  refine ⟨Mlin hI hA, ⟨hbij, hcont, ?_⟩, fun ϕ s hs => ⟨integrable_psi hI hA ϕ s hs, ?_⟩⟩
  · exact IsOpenMap.of_inverse hsymm (fun y => e.apply_symm_apply y)
      (fun x => e.symm_apply_apply x)
  · show Mfun ϕ s = _
    simp only [Mfun, if_pos hs]
