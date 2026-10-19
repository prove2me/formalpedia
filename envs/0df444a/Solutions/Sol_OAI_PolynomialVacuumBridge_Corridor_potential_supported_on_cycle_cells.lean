-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.potential_supported_on_cycle_cells
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:35:15.847665+00:00
-- url     : https://prove2.me/submissions/8e27c335-c408-4552-96bc-8666b8081827

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/PotentialSupport.lean:L43-L94
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.potential_supported_on_cycle_cells. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_finite_gradient_injective

-- ---- from OAI.Combinatorics.HoneycombCorridor.Currents ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem local_contour_current (p : EdgeIndex →₀ ℤ) (q : EdgeIndex → ℚ)
    (hq : ConservedCurrent q) (hs : ∀ e, p e = 0 → q e = 0)
    (g : Germ) (b : Bool) (hl : LocalContour p g b) :
    directedCurrent q (advance g b) = directedCurrent q g ∧
      ∀ k : Fin 3, directedCurrent q (g.1,k) =
        -directedCurrent q g * (orientedFlow p (g.1,k) : ℚ) := by
  have hz (k : Fin 3) :
      (if k = outgoingSlot g b then (1 : ℤ) else 0) -
        (if k = g.2 then 1 else 0) = 0 → directedCurrent q (g.1,k) = 0 := by
    intro h
    have h0 : orientedFlow p (g.1,k) = 0 := (hl k).trans h
    have he := hs (edgeOf (g.1,k)) ((orientedFlow_zero_iff p _).mp h0)
    simp [directedCurrent,he]
  have hsum := hq g.1
  rw [directedCurrent_advance]
  constructor
  · rcases g with ⟨v,k⟩
    have hz0 := hz 0
    have hz1 := hz 1
    have hz2 := hz 2
    fin_cases k <;> cases b <;>
      simp [outgoingSlot,Fin.sum_univ_succ] at hz0 hz1 hz2 hsum ⊢ <;> linarith
  · intro k
    rw [hl k]
    rcases g with ⟨v,l⟩
    have hz0 := hz 0
    have hz1 := hz 1
    have hz2 := hz 2
    fin_cases l <;> cases b <;> fin_cases k <;>
      simp [outgoingSlot,Fin.sum_univ_succ] at hz0 hz1 hz2 hsum ⊢ <;> linarith

theorem word_contour_current (p : EdgeIndex →₀ ℤ) (q : EdgeIndex → ℚ)
    (hq : ConservedCurrent q) (hs : ∀ e, p e = 0 → q e = 0)
    (g : Germ) (w : List Bool) (hw : WordContour p g w) :
    directedCurrent q (terminalGerm g w) = directedCurrent q g ∧
    ∀ e : EdgeIndex, wordFlow g w e ≠ 0 →
      q e = -directedCurrent q g * (p e : ℚ) := by
  induction w generalizing g with
  | nil => simp [terminalGerm,wordFlow]
  | cons b w ih =>
      obtain ⟨hstep,hlocal⟩ := local_contour_current p q hq hs g b hw.1
      obtain ⟨hend,hedge⟩ := ih (advance g b) hw.2
      constructor
      · exact hend.trans hstep
      · intro e he
        by_cases ht : wordFlow (advance g b) w e ≠ 0
        · simpa only [hstep] using hedge e ht
        · have hd : dartFlow (g.1,outgoingSlot g b) e ≠ 0 := by
            simpa only [wordFlow,Finsupp.add_apply,not_not.mp ht,add_zero] using he
          have heq : e = edgeOf (g.1,outgoingSlot g b) := by
            by_contra h
            exact hd (by simp [dartFlow,h])
          subst e
          have h := hlocal (outgoingSlot g b)
          rcases g with ⟨v,k⟩
          cases v <;>
            simp [directedCurrent,dartSign,edgeOf,orientedFlow_up,orientedFlow_down] at h ⊢ <;>
            linarith

theorem simple_cycle_current_scalar (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (q : EdgeIndex → ℚ) (hq : ConservedCurrent q)
    (hs : ∀ e, wordFlow g w e = 0 → q e = 0) :
    ∃ c : ℚ, ∀ e, q e = c * (wordFlow g w e : ℚ) := by
  refine ⟨-directedCurrent q g,?_⟩
  intro e
  by_cases he : wordFlow g w e = 0
  · simp [hs e he,he]
  · exact (word_contour_current _ q hq hs g w
      (simple_closed_word_contour g w hN hc)).2 e he

theorem directedCurrent_gradient (r : FaceIndex → ℚ) (g : Germ) :
    directedCurrent (faceGradient r) g = r (leftFace g) - r (rightFace g) := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;>
    simp [directedCurrent,faceGradient,dartSign,edgeOf,canonicalDart,upEnd,
      leftFace,rightFace,reverseGerm,neighbor]

theorem gradient_conserved (r : FaceIndex → ℚ) : ConservedCurrent (faceGradient r) := by
  intro v
  simp only [directedCurrent_gradient]
  cases v <;> simp [Fin.sum_univ_succ,leftFace,rightFace,reverseGerm,neighbor] <;> ring

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.PotentialSupport ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem potential_supported_on_cycle_cells (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w)) (hpne : p ≠ 0)
    (r : FaceIndex →₀ ℚ)
    (hr : ∀ e, e ∉ cellEdges p.support → faceGradient r e = 0) :
    r.support ⊆ p.support := by
  classical
  let pQ : FaceIndex →₀ ℚ := p.mapRange (fun x : ℤ => (x : ℚ)) (by norm_num)
  let rOut : FaceIndex →₀ ℚ := r.filter (fun a => p a = 0)
  have hpQ (e : EdgeIndex) : faceGradient pQ e = (wordFlow g w e : ℚ) := by
    have h := hp (canonicalDart e)
    rcases e with ⟨⟨i,j⟩,k⟩
    simp only [canonicalDart,upEnd,orientedFlow_up] at h
    simp only [faceGradient,pQ,Finsupp.mapRange_apply]
    exact_mod_cast h.symm
  have hOut : ∀ e, wordFlow g w e = 0 → faceGradient rOut e = 0 := by
    intro e he
    have hpE := hp (canonicalDart e)
    have hz : p (leftFace (canonicalDart e)) = p (rightFace (canonicalDart e)) := by
      rcases e with ⟨⟨i,j⟩,k⟩
      simp only [canonicalDart,upEnd,orientedFlow_up,he] at hpE
      simp only [canonicalDart,upEnd]
      omega
    by_cases hl : p (leftFace (canonicalDart e)) = 0
    · have hrz : p (rightFace (canonicalDart e)) = 0 := hz ▸ hl
      have hout : e ∉ cellEdges p.support := by
        simp [mem_cellEdges,Finsupp.mem_support_iff,hl,hrz]
      simpa [faceGradient,rOut,Finsupp.filter_apply,hl,hrz] using hr e hout
    · have hrz : p (rightFace (canonicalDart e)) ≠ 0 := hz ▸ hl
      simp [faceGradient,rOut,hl,hrz]
  obtain ⟨c,hc'⟩ := simple_cycle_current_scalar g w hN hc
    (faceGradient rOut) (gradient_conserved rOut) hOut
  have hEq : rOut = c • pQ := by
    apply finite_gradient_injective
    funext e
    rw [hc' e,← hpQ e]
    simp only [faceGradient,Finsupp.smul_apply,smul_eq_mul]
    ring
  obtain ⟨a,ha⟩ := Finsupp.support_nonempty_iff.mpr hpne
  have hpa : p a ≠ 0 := Finsupp.mem_support_iff.mp ha
  have hpQa : pQ a ≠ 0 := by
    simpa only [pQ,Finsupp.mapRange_apply,ne_eq,Int.cast_eq_zero] using hpa
  have hval := congrArg (fun f : FaceIndex →₀ ℚ => f a) hEq
  simp only [rOut,Finsupp.filter_apply,ite_eq_right hpa,Finsupp.smul_apply,smul_eq_mul] at hval
  have hcz : c = 0 := (mul_eq_zero.mp hval.symm).resolve_right hpQa
  have hR : rOut = 0 := by simpa [hcz] using hEq
  intro a ha
  by_contra hnot
  have hpz : p a = 0 := by simpa only [Finsupp.mem_support_iff,not_not] using hnot
  have hz := congrArg (fun f : FaceIndex →₀ ℚ => f a) hR
  simp only [rOut,Finsupp.filter_apply,ite_eq_left hpz,Finsupp.zero_apply] at hz
  exact (Finsupp.mem_support_iff.mp ha) hz

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.potential_supported_on_cycle_cells := @_root_.OAI.PolynomialVacuumBridge.Corridor.potential_supported_on_cycle_cells
