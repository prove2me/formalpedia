-- Prove2me | solution 1 for IntLInfty.Kan.fillers_tauLe_tauLt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T04:04:34.562178+00:00
-- url     : https://prove2.me/submissions/5cffe128-3d5c-4369-b875-4b0e52aeecb6

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ
import Theorems.Thm_IntLInfty_Kan_postnikov_genAlg_delta_closed
import Theorems.Thm_IntLInfty_Kan_volterra_chart
import Theorems.Thm_IntLInfty_Kan_volterra_chart_contraction
import Theorems.Thm_IntLInfty_Kan_linear_horn_filler_ambient
import Theorems.Thm_IntLInfty_Kan_faceCr_continuousLinear
import Theorems.Thm_IntLInfty_Kan_fillerAt_zero_abs
import Theorems.Thm_IntLInfty_Kan_tauLe_gmap_fibre_affine
import Theorems.Thm_IntLInfty_Kan_fillers_horn_transport

/-! Reduction for `IntLInfty.Kan.fillers_tauLe_tauLt` (horn fillers for `∫τ≤ₙ → ∫τ<ₙ`).
Horn `0`: the abstract fibre filler (`fillerAt_zero_abs`) applied to the Volterra chart `G, H` of
`volterra_chart` (with the contraction bound of `volterra_chart_contraction`), the linear horn
filler of `linear_horn_filler_ambient`, and the fibre projection `π = H` (`n = 0`) or
`π = 1 - s ∘ res` with `s` a continuous linear section of `res` (`n ≥ 1`, affinity of `G` along
`ker res` from `tauLe_gmap_fibre_affine`). Every other horn: `fillers_horn_transport`.
Slice of scratch/probe/a83e3b53.lean L10664-10729, L11005-11013, L11761-11817 (concrete
`Gmap`/`HAmb` replaced by the children's existential `G`, `H`). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ContDiff

namespace IntLInfty.Kan.A83K1T

open IntLInfty.Kan

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

/-- `res` as a continuous linear map. -/
noncomputable def resCLM {S S' : GenSys L} (h : ∀ i, S' i ≤ S i) (r m : ℕ) :
    Amb r S m →L[ℝ] Amb r S' m where
  toFun := res h
  map_add' z w := funext fun t => funext fun k => by
    show ∑ l, _ • (z + w) t l = (∑ l, _ • z t l) + ∑ l, _ • w t l
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => smul_add _ _ _
  map_smul' c z := funext fun t => funext fun k => by
    show ∑ l, _ • (c • z) t l = c • ∑ l, _ • z t l
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => smul_comm (_ : ℝ) c (z t l)
  cont := continuous_pi fun t => continuous_pi fun k =>
    continuous_finset_sum _ fun l _ =>
      (continuous_const_smul ((genBasis S t).repr (Submodule.inclusion (h t) (genBasis S' t k)) l)).comp
        ((continuous_apply l).comp (continuous_apply t))

theorem faceAmb_sub {r : ℕ} (hr : 1 ≤ r) (S : GenSys L) (m : ℕ) (i : Fin (m + 2))
    (a b : Amb r S (m + 1)) :
    faceAmb r S m i (a - b) = faceAmb r S m i a - faceAmb r S m i b := by
  funext t k
  obtain ⟨F, hF⟩ := (faceCr_continuousLinear r hr ((t : ℕ) + 1)).1 m i
  show faceCr r m ((t : ℕ) + 1) i (a t.castSucc k - b t.castSucc k) =
    faceCr r m ((t : ℕ) + 1) i (a t.castSucc k) - faceCr r m ((t : ℕ) + 1) i (b t.castSucc k)
  rw [← hF, ← hF, ← hF]
  exact F.map_sub _ _

theorem faceAmb_zero {r : ℕ} (hr : 1 ≤ r) (S : GenSys L) (m : ℕ) (i : Fin (m + 2)) :
    faceAmb r S m i (0 : Amb r S (m + 1)) = 0 := by
  have := faceAmb_sub hr S m i 0 0
  rwa [sub_self, sub_self] at this

theorem faceAmb_res {r : ℕ} (hr : 1 ≤ r) {S S' : GenSys L} (h : ∀ i, S' i ≤ S i) (m : ℕ)
    (i : Fin (m + 2)) (z : Amb r S (m + 1)) :
    faceAmb r S' m i (res h z) = res h (faceAmb r S m i z) := by
  funext t k
  obtain ⟨F, hF⟩ := (faceCr_continuousLinear r hr ((t : ℕ) + 1)).1 m i
  show faceCr r m ((t : ℕ) + 1) i (∑ l, _ • z t.castSucc l) =
    ∑ l, _ • faceCr r m ((t : ℕ) + 1) i (z t.castSucc l)
  simp only [← hF]
  rw [map_sum]
  exact Finset.sum_congr rfl fun l _ => map_smul _ _ _

/-- `res ∘ G = G' ∘ res` makes `DG` preserve `ker res`. -/
theorem res_fderiv_of_comm {r m : ℕ} {S S' : GenSys L} (h : ∀ i, S' i ≤ S i)
    (G : Amb r S m → Amb r S m) (G' : Amb r S' m → Amb r S' m)
    (hGc : ContDiff ℝ ∞ G) (hGc' : ContDiff ℝ ∞ G')
    (hc : ∀ z, res h (G z) = G' (res h z)) (z v : Amb r S m) (hv : res h v = 0) :
    res h (fderiv ℝ G z v) = 0 := by
  have hG := hGc.differentiable (by simp) z
  have hG' := hGc'.differentiable (by simp) (resCLM h r m z)
  have h1 : HasFDerivAt (fun w => resCLM h r m (G w))
      ((resCLM h r m).comp (fderiv ℝ G z)) z :=
    (resCLM h r m).hasFDerivAt.comp z hG.hasFDerivAt
  have h2 : HasFDerivAt (fun w => G' (resCLM h r m w))
      ((fderiv ℝ G' (resCLM h r m z)).comp (resCLM h r m)) z :=
    hG'.hasFDerivAt.comp z (resCLM h r m).hasFDerivAt
  have e : (fun w => resCLM h r m (G w)) = fun w => G' (resCLM h r m w) :=
    funext fun w => hc w
  rw [e] at h1
  have := congrArg (fun T => T v) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply] at this
  have hv' : resCLM h r m v = 0 := hv
  show resCLM h r m (fderiv ℝ G z v) = 0
  rw [this, hv', map_zero]

/-- `π = 1 - s ∘ res` for a continuous linear section `s` of `res`. -/
noncomputable def piOf {r m : ℕ} {S S' : GenSys L} (h : ∀ i, S' i ≤ S i)
    (s : Amb r S' m →L[ℝ] Amb r S m) : Amb r S m →L[ℝ] Amb r S m :=
  ContinuousLinearMap.id ℝ _ - s.comp (resCLM h r m)

theorem piOf_apply {r m : ℕ} {S S' : GenSys L} (h : ∀ i, S' i ≤ S i)
    (s : Amb r S' m →L[ℝ] Amb r S m) (x : Amb r S m) : piOf h s x = x - s (res h x) := rfl

theorem res_piOf {r m : ℕ} {S S' : GenSys L} (h : ∀ i, S' i ≤ S i)
    (s : Amb r S' m →L[ℝ] Amb r S m) (hs : ∀ y, res h (s y) = y) (x : Amb r S m) :
    res h (piOf h s x) = 0 := by
  rw [piOf_apply]
  have e : res h (x - s (res h x)) = res h x - res h (s (res h x)) := map_sub (resCLM h r m) _ _
  rw [e, hs, sub_self]

theorem piOf_eq_iff {r m : ℕ} {S S' : GenSys L} (h : ∀ i, S' i ≤ S i)
    (s : Amb r S' m →L[ℝ] Amb r S m) (hs : ∀ y, res h (s y) = y) (v : Amb r S m) :
    piOf h s v = v ↔ res h v = 0 := by
  constructor
  · intro hv; rw [← hv]; exact res_piOf h s hs v
  · intro hv; rw [piOf_apply, hv, map_zero, sub_zero]

theorem piOf_idem {r m : ℕ} {S S' : GenSys L} (h : ∀ i, S' i ≤ S i)
    (s : Amb r S' m →L[ℝ] Amb r S m) (hs : ∀ y, res h (s y) = y) (x : Amb r S m) :
    piOf h s (piOf h s x) = piOf h s x :=
  (piOf_eq_iff h s hs _).2 (res_piOf h s hs x)

theorem tauLe_eq_bot (δ : LInfty L) {n i : ℕ} (h : n < i) : tauLe δ n i = ⊥ := by
  unfold tauLe
  rw [if_neg (by omega), if_neg (by omega)]

theorem finrank_tauLe_gt (δ : LInfty L) (n : ℕ) :
    ∀ t, n < t → Module.finrank ℝ (tauLe δ n t) = 0 := fun t h => by
  rw [tauLe_eq_bot δ h]
  exact finrank_bot ℝ _

theorem tauLt_zero_eq_bot (δ : LInfty L) (t : ℕ) : tauLt δ 0 t = ⊥ := by
  unfold tauLt
  split_ifs with h1 h0
  · exact absurd h1 (Nat.not_lt_zero _)
  · subst h0; rfl
  · rfl

/-- (K1e) horn-`0` fillers for `∫ τ≤n → ∫ τ<n`, every `n`. -/
theorem filler_zero {r : ℕ} (hr : 1 ≤ r) (δ : LInfty L) (n : ℕ)
    (h : ∀ i, tauLt δ n i ≤ tauLe δ n i) (m : ℕ) :
    ∃ σ : Amb r (tauLe δ n) (m + 1) →
        (({i : Fin (m + 2) // i ≠ 0} → Amb r (tauLe δ n) m) × Amb r (tauLt δ n) (m + 1)) →
        Amb r (tauLe δ n) (m + 1),
      (∀ x, ContDiff ℝ ∞ (σ x)) ∧
      (∀ x ∈ integ r δ (tauLe δ n) (m + 1), ∀ y ∈ RelHorn r δ h m 0,
          σ x y ∈ integ r δ (tauLe δ n) (m + 1) ∧ kanMap h m 0 (σ x y) = y) ∧
      (∀ x ∈ integ r δ (tauLe δ n) (m + 1), σ x (kanMap h m 0 x) = x) := by
  obtain ⟨-, -, hclLe, hclLt, -⟩ := postnikov_genAlg_delta_closed L δ
  obtain ⟨G, H, hGH⟩ := volterra_chart r hr L δ
  obtain ⟨hGv, hcomp, hGc, hHid, -, hHD, hint, hGf, hHf, hAff, hresGH⟩ :=
    hGH (tauLe δ n) (hclLe n)
  obtain ⟨-, -, hGc', -, -, -, hint', -, -, -, -⟩ := hGH (tauLt δ n) (hclLt n)
  haveI := hcomp (m + 1)
  haveI := hcomp m
  have hZ := (linear_horn_filler_ambient r hr L (tauLe δ n) (tauLt δ n) h).1 m 0
  obtain ⟨Z, hZc, hZres, hZface, hZkan⟩ := hZ
  have hV : ∀ (q : ℕ) (x : Amb r (tauLe δ n) q),
      ∃ k : ℕ, ‖(fderiv ℝ (G (tauLe δ n) q) x) ^ k‖ < 1 := fun q x =>
    volterra_chart_contraction r hr L δ (tauLe δ n) (hclLe n) (G (tauLe δ n)) hGv hGc q x
  have hFsub : ∀ (i : Fin (m + 2)) (a b : Amb r (tauLe δ n) (m + 1)),
      faceAmb r (tauLe δ n) m i (a - b) = faceAmb r (tauLe δ n) m i a - faceAmb r (tauLe δ n) m i b :=
    fun i a b => faceAmb_sub hr (tauLe δ n) m i a b
  have hRsub : ∀ a b : Amb r (tauLe δ n) (m + 1), res h (a - b) = res h a - res h b :=
    fun a b => (resCLM h r (m + 1)).map_sub a b
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine fillerAt_zero_abs δ h (G _ (m + 1)) (G _ m) (H _ (m + 1)) (H _ m) Z (hGc _)
      (hV _) (hV _) (hGf m) (hint _) (hint _) (hHid _) (hHf m) hFsub hRsub hZc hZres hZface hZkan
      (H _ (m + 1)) (H _ m) (hHid _) (hHid _) (fun z v _ => hHD _ z v) (fun z v _ => hHD _ z v)
      (fun z v hv => hAff (finrank_tauLe_gt δ 0) _ z v hv)
      (fun z v hv => hAff (finrank_tauLe_gt δ 0) _ z v hv) ?_ ?_ ?_
    · intro i hi v hv
      rw [← hHf m i hi v, hv]
    · intro v _
      funext t k
      exfalso
      have hf : Module.finrank ℝ (tauLt δ 0 (t : ℕ)) = 0 := by
        rw [tauLt_zero_eq_bot]; exact finrank_bot ℝ _
      exact Nat.not_lt_zero _ (lt_of_lt_of_eq k.2 hf)
    · intro z0 _
      exact hHid _ _
  · obtain ⟨s1, hs1⟩ := (linear_horn_filler_ambient r hr L (tauLe δ n) (tauLt δ n) h).2 (m + 1)
    obtain ⟨s0, hs0⟩ := (linear_horn_filler_ambient r hr L (tauLe δ n) (tauLt δ n) h).2 m
    have hI : ∀ (q : ℕ) (s : Amb r (tauLt δ n) q →L[ℝ] Amb r (tauLe δ n) q)
        (hs : ∀ y, res h (s y) = y) (z v : Amb r (tauLe δ n) q), piOf h s v = v →
        piOf h s (fderiv ℝ (G _ q) z v) = fderiv ℝ (G _ q) z v := fun q s hs z v hv =>
      (piOf_eq_iff h s hs _).2 (res_fderiv_of_comm h _ _ (hGc q) (hGc' q)
        (fun w => (hresGH (tauLt δ n) h (hclLt n) q w).1) z v ((piOf_eq_iff h s hs v).1 hv))
    have hA : ∀ (q : ℕ) (s : Amb r (tauLt δ n) q →L[ℝ] Amb r (tauLe δ n) q)
        (hs : ∀ y, res h (s y) = y) (z v : Amb r (tauLe δ n) q), piOf h s v = v →
        G _ q (z + v) = G _ q z + fderiv ℝ (G _ q) z v := fun q s hs z v hv =>
      tauLe_gmap_fibre_affine r hr L δ n hn h (G (tauLe δ n)) hGv hGc q z v
        ((piOf_eq_iff h s hs v).1 hv)
    refine fillerAt_zero_abs δ h (G _ (m + 1)) (G _ m) (H _ (m + 1)) (H _ m) Z (hGc _)
      (hV _) (hV _) (hGf m) (hint _) (hint _) (hHid _) (hHf m) hFsub hRsub hZc hZres hZface hZkan
      (piOf h s1) (piOf h s0) (piOf_idem h s1 hs1) (piOf_idem h s0 hs0)
      (hI _ s1 hs1) (hI _ s0 hs0) (hA _ s1 hs1) (hA _ s0 hs0) ?_ ?_ ?_
    · intro i hi v hv
      rw [piOf_eq_iff h s1 hs1] at hv
      rw [piOf_eq_iff h s0 hs0, ← faceAmb_res hr h m i v, hv]
      exact faceAmb_zero hr (tauLt δ n) m i
    · intro v hv
      exact (piOf_eq_iff h s1 hs1 v).1 hv
    · intro z0 hz0
      rw [piOf_eq_iff h s1 hs1, (hresGH (tauLt δ n) h (hclLt n) (m + 1) _).2, hRsub,
        (hresGH (tauLt δ n) h (hclLt n) (m + 1) z0).1]
      exact (hint' (m + 1) (res h z0)).1 hz0

end IntLInfty.Kan.A83K1T

open IntLInfty.Kan in
theorem solution (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) (n : ℕ)
    (h : ∀ i, tauLt δ n i ≤ tauLe δ n i) (m : ℕ) (j : Fin (m + 2)) :
    ∃ σ : Amb r (tauLe δ n) (m + 1) → (({i : Fin (m + 2) // i ≠ j} → Amb r (tauLe δ n) m) × Amb r (tauLt δ n) (m + 1)) →
        Amb r (tauLe δ n) (m + 1),
      (∀ x, ContDiff ℝ ∞ (σ x)) ∧
      (∀ x ∈ integ r δ (tauLe δ n) (m + 1), ∀ y ∈ RelHorn r δ h m j,
          σ x y ∈ integ r δ (tauLe δ n) (m + 1) ∧ kanMap h m j (σ x y) = y) ∧
      (∀ x ∈ integ r δ (tauLe δ n) (m + 1), σ x (kanMap h m j x) = x) :=
  fillers_horn_transport r hr L δ (tauLe δ n) (tauLt δ n) h m j (A83K1T.filler_zero hr δ n h m)
