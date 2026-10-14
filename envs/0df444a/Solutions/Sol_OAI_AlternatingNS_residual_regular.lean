-- Prove2me | solution 1 for OAI.AlternatingNS.residual_regular
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T02:26:42.817032+00:00
-- url     : https://prove2.me/submissions/236eb2f6-deb1-47a2-b181-b2c96b8bbd28

import Mathlib
import Definitions.Def_NavierStokesAlternating
set_option autoImplicit false
open scoped BigOperators ENNReal Topology ContDiff
open MeasureTheory OAI OAI.AlternatingNS

namespace AN_F2
noncomputable section
set_option linter.unusedSectionVars false

abbrev HS : Set (ℝ × Space) := Set.Ici 0 ×ˢ Set.univ

lemma uniqueDiffOn_HS : UniqueDiffOn ℝ HS := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

lemma mem_HS {t : ℝ} {x : Space} (ht : 0 ≤ t) : ((t, x) : ℝ × Space) ∈ HS := ⟨ht, trivial⟩

lemma top_add_one_le : (((⊤ : ℕ∞) : ℕ∞ω) + 1 ≤ ((⊤ : ℕ∞) : ℕ∞ω)) := by norm_cast

lemma top_ne_zero' : (((⊤ : ℕ∞) : ℕ∞ω) ≠ 0) := by simp

lemma minSmooth_le : minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
  rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top

lemma closure_interior_HS : closure (interior HS) = HS := by
  simp [HS, interior_prod_eq, closure_prod_eq, closure_Ioi]

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- equality on the closed half-space -/
def Eqv (F G : ℝ → Space → E) : Prop := ∀ t, 0 ≤ t → ∀ x, F t x = G t x

lemma Eqv.refl (F : ℝ → Space → E) : Eqv F F := fun _ _ _ => rfl
lemma Eqv.symm {F G : ℝ → Space → E} (h : Eqv F G) : Eqv G F :=
  fun t ht x => (h t ht x).symm
lemma Eqv.trans {F G H : ℝ → Space → E} (h : Eqv F G) (h' : Eqv G H) : Eqv F H :=
  fun t ht x => (h t ht x).trans (h' t ht x)

/-- directional derivative within the half-space -/
def Dd (v : ℝ × Space) (F : ℝ → Space → E) : ℝ → Space → E :=
  fun t x => fderivWithin ℝ (Function.uncurry F) HS (t, x) v

lemma uncurry_Dd (v : ℝ × Space) (F : ℝ → Space → E) :
    Function.uncurry (Dd v F) = fun z => fderivWithin ℝ (Function.uncurry F) HS z v := by
  funext z; rfl

lemma smooth_congr {F G : ℝ → Space → E} (hF : Smooth F) (h : Eqv F G) : Smooth G := by
  refine hF.congr ?_
  rintro ⟨t, x⟩ ⟨ht, -⟩
  exact (h t ht x).symm

lemma smooth_Dd {F : ℝ → Space → E} (hF : Smooth F) (v : ℝ × Space) : Smooth (Dd v F) := by
  unfold Smooth
  rw [uncurry_Dd]
  exact (hF.fderivWithin uniqueDiffOn_HS top_add_one_le).clm_apply contDiffOn_const

lemma diffWithin {F : ℝ → Space → E} (hF : Smooth F) {z : ℝ × Space} (hz : z ∈ HS) :
    DifferentiableWithinAt ℝ (Function.uncurry F) HS z :=
  hF.differentiableOn top_ne_zero' z hz

lemma Dd_congr {F G : ℝ → Space → E} (h : Eqv F G) (v : ℝ × Space) : Eqv (Dd v F) (Dd v G) := by
  intro t ht x
  simp only [Dd]
  rw [fderivWithin_congr (f := Function.uncurry G)]
  · rintro ⟨s, y⟩ ⟨hs, -⟩
    exact h s hs y
  · exact h t ht x

lemma dt_congr {F G : ℝ → Space → E} (h : Eqv F G) : Eqv (dt F) (dt G) := by
  intro t ht x
  simp only [dt]
  rw [fderivWithin_congr (f := fun s => G s x)]
  · intro s hs
    exact h s hs x
  · exact h t ht x

lemma dx_congr {F G : ℝ → Space → E} (h : Eqv F G) (i : Fin 3) : Eqv (dx i F) (dx i G) := by
  intro t ht x
  simp only [dx]
  have : F t = G t := funext (h t ht)
  rw [this]

lemma dt_eq_Dd {F : ℝ → Space → E} (hF : Smooth F) : Eqv (dt F) (Dd ((1 : ℝ), (0 : Space)) F) := by
  intro t ht x
  have hd := (diffWithin hF (mem_HS (x := x) ht)).hasFDerivWithinAt
  have hh : HasFDerivWithinAt (fun s : ℝ => ((s, x) : ℝ × Space))
      ((ContinuousLinearMap.id ℝ ℝ).prod 0) (Set.Ici 0) t :=
    ((hasFDerivAt_id t).prodMk (hasFDerivAt_const x t)).hasFDerivWithinAt
  have hc := hd.comp t hh (fun s hs => mem_HS hs)
  have := hc.fderivWithin (uniqueDiffOn_Ici 0 t ht)
  simp only [dt, Dd]
  rw [show (fun s => F s x) = (Function.uncurry F ∘ fun s : ℝ => ((s, x) : ℝ × Space)) from rfl,
    this]
  simp

lemma dx_eq_Dd {F : ℝ → Space → E} (hF : Smooth F) (i : Fin 3) :
    Eqv (dx i F) (Dd ((0 : ℝ), e i) F) := by
  intro t ht x
  have hd := (diffWithin hF (mem_HS (x := x) ht)).hasFDerivWithinAt
  have hh : HasFDerivWithinAt (fun y : Space => ((t, y) : ℝ × Space))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) Set.univ x :=
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)).hasFDerivWithinAt
  have hc := hd.comp x hh (fun y _ => mem_HS ht)
  rw [hasFDerivWithinAt_univ] at hc
  have := hc.fderiv
  simp only [dx, Dd]
  rw [show F t = (Function.uncurry F ∘ fun y : Space => ((t, y) : ℝ × Space)) from rfl, this]
  simp


lemma Dd_Dd {F : ℝ → Space → E} (hF : Smooth F) (v w : ℝ × Space) {t : ℝ} (ht : 0 ≤ t)
    (x : Space) :
    Dd v (Dd w F) t x =
      fderivWithin ℝ (fderivWithin ℝ (Function.uncurry F) HS) HS (t, x) v w := by
  have hΦ : DifferentiableWithinAt ℝ (fderivWithin ℝ (Function.uncurry F) HS) HS (t, x) :=
    (hF.fderivWithin uniqueDiffOn_HS top_add_one_le).differentiableOn top_ne_zero' _
      (mem_HS ht)
  simp only [Dd]
  rw [show Function.uncurry (Dd w F) = fun z => fderivWithin ℝ (Function.uncurry F) HS z w
    from uncurry_Dd w F]
  rw [fderivWithin_clm_apply (uniqueDiffOn_HS _ (mem_HS ht)) hΦ
    (differentiableWithinAt_const w)]
  simp

lemma Dd_comm {F : ℝ → Space → E} (hF : Smooth F) (v w : ℝ × Space) :
    Eqv (Dd v (Dd w F)) (Dd w (Dd v F)) := by
  intro t ht x
  rw [Dd_Dd hF v w ht, Dd_Dd hF w v ht]
  have hs := (hF (t, x) (mem_HS ht)).isSymmSndFDerivWithinAt minSmooth_le uniqueDiffOn_HS
    (by rw [closure_interior_HS]; exact mem_HS ht) (mem_HS ht)
  exact hs v w

lemma Dd_add {F G : ℝ → Space → E} (hF : Smooth F) (hG : Smooth G) (v : ℝ × Space) :
    Eqv (Dd v (fun t x => F t x + G t x)) (fun t x => Dd v F t x + Dd v G t x) := by
  intro t ht x
  simp only [Dd]
  rw [show Function.uncurry (fun t x => F t x + G t x) =
      Function.uncurry F + Function.uncurry G from rfl]
  rw [fderivWithin_add (uniqueDiffOn_HS _ (mem_HS ht)) (diffWithin hF (mem_HS ht))
    (diffWithin hG (mem_HS ht))]
  rfl

lemma Dd_smul {F : ℝ → Space → E} (hF : Smooth F) (c : ℝ) (v : ℝ × Space) :
    Eqv (Dd v (fun t x => c • F t x)) (fun t x => c • Dd v F t x) := by
  intro t ht x
  simp only [Dd]
  rw [show Function.uncurry (fun t x => c • F t x) = c • Function.uncurry F from rfl]
  rw [fderivWithin_const_smul (uniqueDiffOn_HS _ (mem_HS ht)) (diffWithin hF (mem_HS ht))]
  rfl

lemma smooth_add {F G : ℝ → Space → E} (hF : Smooth F) (hG : Smooth G) :
    Smooth (fun t x => F t x + G t x) := hF.add hG

lemma smooth_smul {F : ℝ → Space → E} (hF : Smooth F) (c : ℝ) :
    Smooth (fun t x => c • F t x) := hF.const_smul c

end

section bil
variable {E₁ E₂ E₃ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]

lemma smooth_bil (B : E₁ →L[ℝ] E₂ →L[ℝ] E₃) {F : ℝ → Space → E₁} {G : ℝ → Space → E₂}
    (hF : Smooth F) (hG : Smooth G) : Smooth (fun t x => B (F t x) (G t x)) :=
  (B.contDiff.comp_contDiffOn hF).clm_apply hG

lemma Dd_bil (B : E₁ →L[ℝ] E₂ →L[ℝ] E₃) {F : ℝ → Space → E₁} {G : ℝ → Space → E₂}
    (hF : Smooth F) (hG : Smooth G) (v : ℝ × Space) :
    Eqv (Dd v (fun t x => B (F t x) (G t x)))
      (fun t x => B (Dd v F t x) (G t x) + B (F t x) (Dd v G t x)) := by
  intro t ht x
  simp only [Dd]
  rw [show Function.uncurry (fun t x => B (F t x) (G t x)) =
      fun z => B (Function.uncurry F z) (Function.uncurry G z) from rfl]
  rw [B.fderivWithin_of_bilinear (diffWithin hF (mem_HS ht)) (diffWithin hG (mem_HS ht))
    (uniqueDiffOn_HS _ (mem_HS ht))]
  simp [add_comm]

end bil


section iter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma smooth_iter {X : ℝ → Space → E} (hX : Smooth X) (v : ℝ × Space) (n : ℕ) :
    Smooth ((Dd v)^[n] X) := by
  induction n with
  | zero => simpa using hX
  | succ n ih => rw [Function.iterate_succ_apply']; exact smooth_Dd ih v

lemma congr_iter {X Y : ℝ → Space → E} (h : Eqv X Y) (v : ℝ × Space) (n : ℕ) :
    Eqv ((Dd v)^[n] X) ((Dd v)^[n] Y) := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply']; exact Dd_congr ih v

lemma comm_iter {X : ℝ → Space → E} (hX : Smooth X) (v w : ℝ × Space) (n : ℕ) :
    Eqv (Dd v ((Dd w)^[n] X)) ((Dd w)^[n] (Dd v X)) := by
  induction n with
  | zero => exact Eqv.refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (Dd_comm (smooth_iter hX w n) v w).trans (Dd_congr ih w)

/-- generic: iterating two operators that agree on smooth fields -/
lemma iter_eqv (op : (ℝ → Space → E) → (ℝ → Space → E)) (v : ℝ × Space)
    (hcongr : ∀ F G, Eqv F G → Eqv (op F) (op G))
    (hagree : ∀ F, Smooth F → Eqv (op F) (Dd v F)) (n : ℕ) {X Y : ℝ → Space → E}
    (hXY : Eqv X Y) (hY : Smooth Y) : Eqv (op^[n] X) ((Dd v)^[n] Y) := by
  induction n with
  | zero => simpa using hXY
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (hcongr _ _ ih).trans (hagree _ (smooth_iter hY v n))

/-- normal form `∂ₜ^l ∂₀^a ∂₁^b ∂₂^c` -/
def Nf (l a b c : ℕ) (X : ℝ → Space → E) : ℝ → Space → E :=
  (Dd ((1 : ℝ), (0 : Space)))^[l] ((Dd ((0 : ℝ), e 0))^[a] ((Dd ((0 : ℝ), e 1))^[b]
    ((Dd ((0 : ℝ), e 2))^[c] X)))

lemma mixed_eqv_Nf {X : ℝ → Space → E} (hX : Smooth X) (l : ℕ) (α : MultiIndex) :
    Eqv (mixed l α X) (Nf l (α 0) (α 1) (α 2) X) := by
  unfold mixed spatial Nf
  have h2 := iter_eqv (dx 2) ((0 : ℝ), e 2) (fun F G h => dx_congr h 2)
    (fun F hF => dx_eq_Dd hF 2) (α 2) (Eqv.refl X) hX
  have s2 := smooth_iter hX ((0 : ℝ), e 2) (α 2)
  have h1 := iter_eqv (dx 1) ((0 : ℝ), e 1) (fun F G h => dx_congr h 1)
    (fun F hF => dx_eq_Dd hF 1) (α 1) h2 s2
  have s1 := smooth_iter s2 ((0 : ℝ), e 1) (α 1)
  have h0 := iter_eqv (dx 0) ((0 : ℝ), e 0) (fun F G h => dx_congr h 0)
    (fun F hF => dx_eq_Dd hF 0) (α 0) h1 s1
  have s0 := smooth_iter s1 ((0 : ℝ), e 0) (α 0)
  exact iter_eqv dt ((1 : ℝ), (0 : Space)) (fun F G h => dt_congr h)
    (fun F hF => dt_eq_Dd hF) l h0 s0

def IsDir (v : ℝ × Space) : Prop := v = ((1 : ℝ), (0 : Space)) ∨ ∃ i : Fin 3, v = ((0 : ℝ), e i)

lemma Dd_Nf {X : ℝ → Space → E} (hX : Smooth X) {v : ℝ × Space} (hv : IsDir v)
    (l a b c : ℕ) : ∃ l' a' b' c' : ℕ, Eqv (Dd v (Nf l a b c X)) (Nf l' a' b' c' X) := by
  set τ : ℝ × Space := ((1 : ℝ), (0 : Space))
  set e0 : ℝ × Space := ((0 : ℝ), e 0)
  set e1 : ℝ × Space := ((0 : ℝ), e 1)
  set e2 : ℝ × Space := ((0 : ℝ), e 2)
  have sC := smooth_iter hX e2 c
  have sB := smooth_iter sC e1 b
  have sA := smooth_iter sB e0 a
  rcases hv with rfl | ⟨i, rfl⟩
  · refine ⟨l + 1, a, b, c, ?_⟩
    unfold Nf
    rw [Function.iterate_succ_apply']
    exact Eqv.refl _
  · fin_cases i
    · refine ⟨l, a + 1, b, c, ?_⟩
      unfold Nf
      refine (comm_iter sA _ τ l).trans ?_
      rw [Function.iterate_succ_apply' _ a]
      exact Eqv.refl _
    · refine ⟨l, a, b + 1, c, ?_⟩
      unfold Nf
      refine (comm_iter sA _ τ l).trans (congr_iter ?_ τ l)
      refine (comm_iter sB _ e0 a).trans (congr_iter ?_ e0 a)
      rw [Function.iterate_succ_apply' _ b]
      exact Eqv.refl _
    · refine ⟨l, a, b, c + 1, ?_⟩
      unfold Nf
      refine (comm_iter sA _ τ l).trans (congr_iter ?_ τ l)
      refine (comm_iter sB _ e0 a).trans (congr_iter ?_ e0 a)
      refine (comm_iter sC _ e1 b).trans (congr_iter ?_ e1 b)
      rw [Function.iterate_succ_apply' _ c]
      exact Eqv.refl _

end iter


section good
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- apply a word of directional derivatives, head innermost -/
def Wd (w : List (ℝ × Space)) (F : ℝ → Space → E) : ℝ → Space → E :=
  w.foldl (fun G v => Dd v G) F

lemma Wd_nil (F : ℝ → Space → E) : Wd [] F = F := rfl
lemma Wd_cons (v : ℝ × Space) (w : List (ℝ × Space)) (F : ℝ → Space → E) :
    Wd (v :: w) F = Wd w (Dd v F) := rfl

lemma Wd_append (w₁ w₂ : List (ℝ × Space)) (F : ℝ → Space → E) :
    Wd (w₁ ++ w₂) F = Wd w₂ (Wd w₁ F) := List.foldl_append

lemma Wd_replicate (v : ℝ × Space) (n : ℕ) (F : ℝ → Space → E) :
    Wd (List.replicate n v) F = (Dd v)^[n] F := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, Wd_cons, ih, Function.iterate_succ_apply]

lemma Wd_congr : ∀ (w : List (ℝ × Space)) {F G : ℝ → Space → E}, Eqv F G → Eqv (Wd w F) (Wd w G)
  | [], _, _, h => h
  | v :: w, _, _, h => Wd_congr w (Dd_congr h v)

lemma smooth_Wd : ∀ (w : List (ℝ × Space)) {F : ℝ → Space → E}, Smooth F → Smooth (Wd w F)
  | [], _, h => h
  | v :: w, _, h => smooth_Wd w (smooth_Dd h v)

lemma Wd_add : ∀ (w : List (ℝ × Space)) {F G : ℝ → Space → E}, Smooth F → Smooth G →
    Eqv (Wd w (fun t x => F t x + G t x)) (fun t x => Wd w F t x + Wd w G t x)
  | [], _, _, _, _ => Eqv.refl _
  | v :: w, _, _, hF, hG =>
    (Wd_congr w (Dd_add hF hG v)).trans (Wd_add w (smooth_Dd hF v) (smooth_Dd hG v))

lemma Wd_smul (c : ℝ) : ∀ (w : List (ℝ × Space)) {F : ℝ → Space → E}, Smooth F →
    Eqv (Wd w (fun t x => c • F t x)) (fun t x => c • Wd w F t x)
  | [], _, _ => Eqv.refl _
  | v :: w, _, hF =>
    (Wd_congr w (Dd_smul hF c v)).trans (Wd_smul c w (smooth_Dd hF v))

def Bdd (F : ℝ → Space → E) : Prop :=
  ∀ J : ℕ, ∃ C : ℝ, ∀ t, 0 ≤ t → ∀ x, (1 + t + ‖x‖) ^ J * ‖F t x‖ ≤ C

lemma weight_nonneg {t : ℝ} (ht : 0 ≤ t) (x : Space) (J : ℕ) : 0 ≤ (1 + t + ‖x‖) ^ J := by
  positivity

lemma Bdd.congr {F G : ℝ → Space → E} (h : Bdd F) (hFG : Eqv F G) : Bdd G := by
  intro J
  obtain ⟨C, hC⟩ := h J
  exact ⟨C, fun t ht x => by rw [← hFG t ht x]; exact hC t ht x⟩

lemma Bdd.add {F G : ℝ → Space → E} (hF : Bdd F) (hG : Bdd G) :
    Bdd (fun t x => F t x + G t x) := by
  intro J
  obtain ⟨C₁, h₁⟩ := hF J
  obtain ⟨C₂, h₂⟩ := hG J
  refine ⟨C₁ + C₂, fun t ht x => ?_⟩
  have hw := weight_nonneg ht x J
  calc (1 + t + ‖x‖) ^ J * ‖F t x + G t x‖
      ≤ (1 + t + ‖x‖) ^ J * (‖F t x‖ + ‖G t x‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hw
    _ = (1 + t + ‖x‖) ^ J * ‖F t x‖ + (1 + t + ‖x‖) ^ J * ‖G t x‖ := by ring
    _ ≤ C₁ + C₂ := add_le_add (h₁ t ht x) (h₂ t ht x)

lemma Bdd.smul {F : ℝ → Space → E} (hF : Bdd F) (c : ℝ) :
    Bdd (fun t x => c • F t x) := by
  intro J
  obtain ⟨C₁, h₁⟩ := hF J
  refine ⟨|c| * C₁, fun t ht x => ?_⟩
  rw [norm_smul, Real.norm_eq_abs]
  calc (1 + t + ‖x‖) ^ J * (|c| * ‖F t x‖) = |c| * ((1 + t + ‖x‖) ^ J * ‖F t x‖) := by ring
    _ ≤ |c| * C₁ := mul_le_mul_of_nonneg_left (h₁ t ht x) (abs_nonneg c)

def Good (F : ℝ → Space → E) : Prop :=
  Smooth F ∧ ∀ w : List (ℝ × Space), (∀ v ∈ w, IsDir v) → Bdd (Wd w F)

lemma Good.congr {F G : ℝ → Space → E} (h : Good F) (hFG : Eqv F G) : Good G :=
  ⟨smooth_congr h.1 hFG, fun w hw => (h.2 w hw).congr (Wd_congr w hFG)⟩

lemma Good.Dd {F : ℝ → Space → E} (h : Good F) {v : ℝ × Space} (hv : IsDir v) :
    Good (Dd v F) := by
  refine ⟨smooth_Dd h.1 v, fun w hw => ?_⟩
  have := h.2 (v :: w) (by
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact hv
    · exact hw u hu)
  simpa [Wd_cons] using this

lemma Good.add {F G : ℝ → Space → E} (hF : Good F) (hG : Good G) :
    Good (fun t x => F t x + G t x) :=
  ⟨smooth_add hF.1 hG.1, fun w hw =>
    ((hF.2 w hw).add (hG.2 w hw)).congr (Wd_add w hF.1 hG.1).symm⟩

lemma Good.smul {F : ℝ → Space → E} (hF : Good F) (c : ℝ) :
    Good (fun t x => c • F t x) :=
  ⟨smooth_smul hF.1 c, fun w hw => ((hF.2 w hw).smul c).congr (Wd_smul c w hF.1).symm⟩

lemma Good.sum3 {F : Fin 3 → ℝ → Space → E} (hF : ∀ i, Good (F i)) :
    Good (fun t x => ∑ i, F i t x) := by
  have : (fun t x => ∑ i, F i t x) = fun t x => (F 0 t x + F 1 t x) + F 2 t x := by
    funext t x; simp [Fin.sum_univ_three]
  rw [this]
  exact ((hF 0).add (hF 1)).add (hF 2)

end good

section goodbil
variable {E₁ E₂ E₃ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]

lemma Bdd.bil (B : E₁ →L[ℝ] E₂ →L[ℝ] E₃) {F : ℝ → Space → E₁} {G : ℝ → Space → E₂}
    (hF : Bdd F) (hG : Bdd G) : Bdd (fun t x => B (F t x) (G t x)) := by
  intro J
  obtain ⟨C₁, h₁⟩ := hF J
  obtain ⟨C₀, h₀⟩ := hG 0
  refine ⟨‖B‖ * (C₁ * C₀), fun t ht x => ?_⟩
  have hw := weight_nonneg ht x J
  have hG0 : ‖G t x‖ ≤ C₀ := by simpa using h₀ t ht x
  have hF1 := h₁ t ht x
  have hnn : 0 ≤ (1 + t + ‖x‖) ^ J * ‖F t x‖ := mul_nonneg hw (norm_nonneg _)
  calc (1 + t + ‖x‖) ^ J * ‖B (F t x) (G t x)‖
      ≤ (1 + t + ‖x‖) ^ J * (‖B‖ * ‖F t x‖ * ‖G t x‖) :=
        mul_le_mul_of_nonneg_left (B.le_opNorm₂ _ _) hw
    _ = ‖B‖ * (((1 + t + ‖x‖) ^ J * ‖F t x‖) * ‖G t x‖) := by ring
    _ ≤ ‖B‖ * (C₁ * C₀) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
        exact mul_le_mul hF1 hG0 (norm_nonneg _) (hnn.trans hF1)

lemma Good.bil (B : E₁ →L[ℝ] E₂ →L[ℝ] E₃) :
    ∀ (w : List (ℝ × Space)), (∀ v ∈ w, IsDir v) →
    ∀ {F : ℝ → Space → E₁} {G : ℝ → Space → E₂}, Good F → Good G →
      Bdd (Wd w (fun t x => B (F t x) (G t x)))
  | [], _, _, _, hF, hG => (hF.2 [] (by simp)).bil B (hG.2 [] (by simp))
  | v :: w, hw, F, G, hF, hG => by
    have hv : IsDir v := hw v (List.mem_cons_self ..)
    have hw' : ∀ u ∈ w, IsDir u := fun u hu => hw u (List.mem_cons_of_mem _ hu)
    rw [Wd_cons]
    have h1 := Wd_congr w (Dd_bil B hF.1 hG.1 v)
    have h2 := Wd_add w (smooth_bil B (smooth_Dd hF.1 v) hG.1)
      (smooth_bil B hF.1 (smooth_Dd hG.1 v))
    have b1 := Good.bil B w hw' (hF.Dd hv) hG
    have b2 := Good.bil B w hw' hF (hG.Dd hv)
    exact (b1.add b2).congr (h1.trans h2).symm

lemma Good.bil' (B : E₁ →L[ℝ] E₂ →L[ℝ] E₃) {F : ℝ → Space → E₁} {G : ℝ → Space → E₂}
    (hF : Good F) (hG : Good G) : Good (fun t x => B (F t x) (G t x)) :=
  ⟨smooth_bil B hF.1 hG.1, fun w hw => Good.bil B w hw hF hG⟩

end goodbil


section final
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma Wd_Nf {X : ℝ → Space → E} (hX : Smooth X) : ∀ (w : List (ℝ × Space)),
    (∀ v ∈ w, IsDir v) → ∀ l a b c : ℕ,
    ∃ l' a' b' c' : ℕ, Eqv (Wd w (Nf l a b c X)) (Nf l' a' b' c' X)
  | [], _, l, a, b, c => ⟨l, a, b, c, Eqv.refl _⟩
  | v :: w, hw, l, a, b, c => by
    have hv : IsDir v := hw v (List.mem_cons_self ..)
    have hw' : ∀ u ∈ w, IsDir u := fun u hu => hw u (List.mem_cons_of_mem _ hu)
    obtain ⟨l₁, a₁, b₁, c₁, h₁⟩ := Dd_Nf hX hv l a b c
    obtain ⟨l₂, a₂, b₂, c₂, h₂⟩ := Wd_Nf hX w hw' l₁ a₁ b₁ c₁
    exact ⟨l₂, a₂, b₂, c₂, (Wd_congr w h₁).trans h₂⟩

lemma good_of_rapid {U : ℝ → Space → Space} (hU : Smooth U) (hr : Rapid U) : Good U := by
  refine ⟨hU, fun w hw => ?_⟩
  obtain ⟨l, a, b, c, h⟩ := Wd_Nf hU w hw 0 0 0 0
  have h' : Eqv (Wd w U) (mixed l ![a, b, c] U) :=
    h.trans (mixed_eqv_Nf hU l ![a, b, c]).symm
  intro J
  obtain ⟨C, -, hC⟩ := hr J l ![a, b, c]
  exact ⟨C, fun t ht x => by rw [h' t ht x]; exact hC t ht x⟩

lemma Nf_eq_Wd (l a b c : ℕ) (X : ℝ → Space → E) :
    Nf l a b c X = Wd (List.replicate c ((0 : ℝ), e 2) ++ List.replicate b ((0 : ℝ), e 1) ++
      List.replicate a ((0 : ℝ), e 0) ++ List.replicate l ((1 : ℝ), (0 : Space))) X := by
  simp only [Wd_append, Wd_replicate, Nf]

lemma rapid_of_good {F : ℝ → Space → Space} (hF : Good F) : Rapid F := by
  intro J l α
  have hw : ∀ v ∈ (List.replicate (α 2) ((0 : ℝ), e 2) ++ List.replicate (α 1) ((0 : ℝ), e 1) ++
      List.replicate (α 0) ((0 : ℝ), e 0) ++ List.replicate l ((1 : ℝ), (0 : Space))), IsDir v := by
    intro v hv
    simp only [List.mem_append, List.mem_replicate] at hv
    rcases hv with ((⟨-, rfl⟩ | ⟨-, rfl⟩) | ⟨-, rfl⟩) | ⟨-, rfl⟩
    · exact Or.inr ⟨2, rfl⟩
    · exact Or.inr ⟨1, rfl⟩
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inl rfl
  obtain ⟨C, hC⟩ := hF.2 _ hw J
  rw [← Nf_eq_Wd] at hC
  have h := mixed_eqv_Nf hF.1 l α
  refine ⟨max C 0, le_max_right _ _, fun t ht x => ?_⟩
  rw [h t ht x]
  exact (hC t ht x).trans (le_max_left _ _)

end final

/-- `u ↦ (u i) • w` as a bilinear map -/
def Bi (i : Fin 3) : Space →L[ℝ] Space →L[ℝ] Space :=
  (ContinuousLinearMap.lsmul ℝ ℝ).comp (EuclideanSpace.proj i)

lemma Bi_apply (i : Fin 3) (u w : Space) : Bi i u w = u i • w := by
  simp [Bi]

lemma advection_eq (U : ℝ → Space → Space) (t : ℝ) (x : Space) :
    advection U t x = ∑ i, Bi i (U t x) (dx i U t x) := by
  simp only [Bi_apply, advection, dx]
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (U t x)]
  simp [map_sum, map_smul, e]


/-- the residual written with half-space directional derivatives -/
def Rres (ν : ℝ) (U : ℝ → Space → Space) : ℝ → Space → Space :=
  fun t x => (Dd ((1 : ℝ), (0 : Space)) U t x + ∑ i, Bi i (U t x) (Dd ((0 : ℝ), e i) U t x)) +
    (-ν) • ∑ i, Dd ((0 : ℝ), e i) (Dd ((0 : ℝ), e i) U) t x

lemma residual_eqv (ν : ℝ) {U : ℝ → Space → Space} (hU : Smooth U) :
    Eqv (residual ν U) (Rres ν U) := by
  intro t ht x
  simp only [AlternatingNS.residual, Rres, laplacian, advection_eq]
  rw [dt_eq_Dd hU t ht x]
  have h1 : ∀ i, dx i U t x = Dd ((0 : ℝ), e i) U t x := fun i => dx_eq_Dd hU i t ht x
  have h2 : ∀ i, dx i (dx i U) t x = Dd ((0 : ℝ), e i) (Dd ((0 : ℝ), e i) U) t x := fun i =>
    (dx_congr (dx_eq_Dd hU i) i t ht x).trans (dx_eq_Dd (smooth_Dd hU _) i t ht x)
  simp only [h1, h2, sub_eq_add_neg, neg_smul]

lemma good_Rres (ν : ℝ) {U : ℝ → Space → Space} (hg : Good U) : Good (Rres ν U) := by
  have gτ : Good (Dd ((1 : ℝ), (0 : Space)) U) := hg.Dd (Or.inl rfl)
  have gadv : Good (fun t x => ∑ i, Bi i (U t x) (Dd ((0 : ℝ), e i) U t x)) :=
    Good.sum3 (F := fun i t x => Bi i (U t x) (Dd ((0 : ℝ), e i) U t x))
      (fun i => Good.bil' (Bi i) hg (hg.Dd (Or.inr ⟨i, rfl⟩)))
  have glap : Good (fun t x => ∑ i, Dd ((0 : ℝ), e i) (Dd ((0 : ℝ), e i) U) t x) :=
    Good.sum3 (F := fun i => Dd ((0 : ℝ), e i) (Dd ((0 : ℝ), e i) U))
      (fun i => (hg.Dd (Or.inr ⟨i, rfl⟩)).Dd (Or.inr ⟨i, rfl⟩))
  exact (gτ.add gadv).add (glap.smul (-ν))

lemma fderiv_vanish {K : Set Space} (hK : IsClosed K) (G : Space → Space)
    (hG : ∀ y, y ∉ K → G y = 0) (y : Space) (hy : y ∉ K) : fderiv ℝ G y = 0 := by
  have hev : G =ᶠ[𝓝 y] fun _ => (0 : Space) :=
    Filter.eventually_of_mem (hK.isOpen_compl.mem_nhds hy) (fun z hz => hG z hz)
  rw [hev.fderiv_eq]
  simp

lemma residual_supported (ν : ℝ) (U : ℝ → Space → Space) (K : Set Space) (hK : IsCompact K)
    (hs : SupportedIn U K) : SupportedIn (residual ν U) K := by
  intro t ht x hx
  by_contra hxK
  apply hx
  have hU0 : ∀ s, 0 ≤ s → ∀ y, y ∉ K → U s y = 0 := fun s hs' y hy =>
    Function.notMem_support.1 (fun h => hy (hs s hs' h))
  have hdt : dt U t x = 0 := by
    simp only [dt]
    rw [fderivWithin_congr (s := Set.Ici (0 : ℝ)) (f := fun _ => (0 : Space))
      (fun s hs' => hU0 s hs' x hxK)
      (hU0 t ht x hxK)]
    simp
  have hadv : advection U t x = 0 := by
    simp [advection, hU0 t ht x hxK]
  have hdx : ∀ i, ∀ y, y ∉ K → dx i U t y = 0 := fun i y hy => by
    simp [dx, fderiv_vanish hK.isClosed (U t) (hU0 t ht) y hy]
  have hlap : laplacian U t x = 0 := by
    simp only [laplacian, dx]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [fderiv_vanish hK.isClosed (dx i U t) (hdx i) x hxK]
    simp
  simp [AlternatingNS.residual, hdt, hadv, hlap]

end
end AN_F2

theorem solution (ν : ℝ) (U : Velocity) (K : Set Space) (hK : IsCompact K)
    (hU : Smooth U) (hs : SupportedIn U K) (hr : Rapid U) :
    Smooth (residual ν U) ∧ SupportedIn (residual ν U) K ∧ Rapid (residual ν U) := by
  have hg : AN_F2.Good (residual ν U) :=
    (AN_F2.good_Rres ν (AN_F2.good_of_rapid hU hr)).congr (AN_F2.residual_eqv ν hU).symm
  exact ⟨hg.1, AN_F2.residual_supported ν U K hK hs, AN_F2.rapid_of_good hg⟩
