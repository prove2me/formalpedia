-- Prove2me | solution 1 for InconsistentDR.Shadow.theorem_6_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T22:54:59.918752+00:00
-- url     : https://prove2.me/submissions/bacb3ed2-2313-48ee-9987-c75e27cbd5c7

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_FRBSplitting_Weak_Setting
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization
import Theorems.Thm_InconsistentDR_Shadow_proposition_6_2
import Theorems.Thm_InconsistentDR_Shadow_proposition_6_5
import Theorems.Thm_InconsistentDR_Shadow_proposition_6_6
import Theorems.Thm_InconsistentDR_Shadow_eq_75_tendsto
import Theorems.Thm_InconsistentDR_Shadow_closure_domConj_eq_closure_ran_subgrad

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization FRBSplitting.Weak
open InconsistentDR.Shadow

theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (Pf Pg : X → X) (hPf : IsResolvent 1 (subgrad f) Pf) (hPg : IsResolvent 1 (subgrad g) Pg)
    (v : X) (hv : IsMinNormPt (closure (Set.range fun x => x - drT Pf Pg x)) v)
    (h12 : Standing12 (subgrad f) (subgrad g) Pf Pg)
    (h0 : (0 : X) ∈ domConj f + domConj g)
    (hvran : v ∈ Set.range fun x => x - drT Pf Pg x)
    (hzer : ∃ x, ∃ a ∈ subgrad f x, ∃ b ∈ subgrad g (x - v), a + b = 0)
    (x : X) :
    ∃ z : X,
      (IsWeakLimit (fun n => Pf ((drT Pf Pg)^[n] x)) z ∧
        ∀ y, f z + g (z - v) ≤ f y + g (y - v)) ∧
      (IsWeakLimit (fun n => Pg (refl Pf ((drT Pf Pg)^[n] x))) (z - v) ∧
        ∀ y, f (z - v + v) + g (z - v) ≤ f (y + v) + g y) ∧
      (Tendsto (fun n => f (Pf ((drT Pf Pg)^[n] x)) + g (Pg (refl Pf ((drT Pf Pg)^[n] x))))
          atTop (𝓝 (f z + g (z - v))) ∧
        f z + g (z - v) = ⨅ y, f y + g (y - v)) ∧
      Tendsto (fun n => f (Pf ((drT Pf Pg)^[n] x))) atTop (𝓝 (f z)) ∧
      Tendsto (fun n => g (Pg (refl Pf ((drT Pf Pg)^[n] x)))) atTop (𝓝 (g (z - v))) := by
  -- Step 1: `0 ∈ cl R`, i.e. `v_R = 0`.
  have hvR : (0 : X) ∈ closure (setR (subgrad f) (subgrad g)) := by
    obtain ⟨a, ha, b, hb, hab⟩ := h0
    have ha' : a ∈ closure (ran (subgrad f)) := by
      rw [← closure_domConj_eq_closure_ran_subgrad f hf]; exact subset_closure ha
    have hb' : b ∈ closure (ran (subgrad g)) := by
      rw [← closure_domConj_eq_closure_ran_subgrad g hg]; exact subset_closure hb
    have := map_mem_closure₂ (f := fun a b : X => a + b) (u := setR (subgrad f) (subgrad g))
      continuous_add ha' hb' (fun a ha b hb => Set.add_mem_add ha hb)
    simpa [hab] using this
  -- Step 2: `Z ≠ ∅`.
  have h62 := proposition_6_2 f g hf hg Pf Pg hPf hPg v hv h12 hvR
  have hZ : (solZ (subgrad f) (subgrad g) v).Nonempty := by
    obtain ⟨x0, a, ha, b, hb, hab⟩ := hzer
    refine ⟨x0, ?_⟩
    rw [h62.1]
    exact ⟨a, ha, b, hb, hab⟩
  -- Step 3: weak convergence of the primal shadows.
  obtain ⟨⟨z, hzlim, hzmin⟩, -⟩ := proposition_6_6 f g hf hg Pf Pg hPf hPg v hv h12 hvR hZ x
  -- Step 4: (75) gives `p n - q n → v`, hence `q n ⇀ z - v`.
  obtain ⟨hid, hlim⟩ := eq_75_tendsto f g hf hg Pf Pg hPf hPg v hv x
  have hdiff : Tendsto (fun n => Pf ((drT Pf Pg)^[n] x) - Pg (refl Pf ((drT Pf Pg)^[n] x)))
      atTop (𝓝 v) := by
    simpa only [hid] using hlim
  have hqlim : IsWeakLimit (fun n => Pg (refl Pf ((drT Pf Pg)^[n] x))) (z - v) := by
    intro u
    have h1 := hzlim u
    have h2 : Tendsto (fun n => inner ℝ (Pf ((drT Pf Pg)^[n] x) -
        Pg (refl Pf ((drT Pf Pg)^[n] x))) u) atTop (𝓝 (inner ℝ v u)) :=
      ((continuous_id.inner continuous_const).tendsto v).comp hdiff
    have h3 := h1.sub h2
    have e1 : ∀ n, inner ℝ (Pf ((drT Pf Pg)^[n] x)) u - inner ℝ (Pf ((drT Pf Pg)^[n] x) -
        Pg (refl Pf ((drT Pf Pg)^[n] x))) u = inner ℝ (Pg (refl Pf ((drT Pf Pg)^[n] x))) u := by
      intro n; rw [inner_sub_left]; ring
    rw [inner_sub_left]
    simpa only [e1] using h3
  -- Step 5: values, via Proposition 6.5.
  have hcl : IsWeakClusterPt (fun n => Pf ((drT Pf Pg)^[n] x)) z :=
    ⟨id, strictMono_id, hzlim⟩
  have h65 := (proposition_6_5 f g hf hg Pf Pg hPf hPg v hv h12 hvR hZ x).2.2 z hcl
  have hmu : f z + g (z - v) = ⨅ y, f y + g (y - v) :=
    le_antisymm (le_iInf hzmin) (iInf_le (fun y => f y + g (y - v)) z)
  refine ⟨z, ⟨hzlim, hzmin⟩, ⟨hqlim, ?_⟩, ⟨?_, hmu⟩, h65.1, h65.2.1⟩
  · intro y
    have := hzmin (y + v)
    simpa using this
  · rw [hmu]; exact h65.2.2
