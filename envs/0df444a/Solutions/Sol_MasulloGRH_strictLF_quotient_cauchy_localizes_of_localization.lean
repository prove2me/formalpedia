-- Prove2me | solution 1 for MasulloGRH.strictLF_quotient_cauchy_localizes_of_localization
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-21T00:22:59.039208+00:00
-- url     : https://prove2.me/submissions/d0ac6922-d13b-461c-8623-f3394e80c547

import Theorems.Thm_MasulloGRH_strictLF_quotient_regular_of_condM_of_localization
import Theorems.Thm_MasulloGRH_nuclear_frechet_quotient_lifts_bounded
import Theorems.Thm_MasulloGRH_strictLF_hlcs_and_closed_steps

set_option autoImplicit false

open MasulloGRH Pointwise

theorem solution (E : Type*) [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hL : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ W ∈ nhds (0 : X m),
      ∃ G ∈ nhds (0 : E ⧸ V), ∀ x ∈ U, Submodule.Quotient.mk (x : E) ∈ G →
        ∃ w ∈ W, ((x : E) - (w : E)) ∈ V)
    (f : Filter (E ⧸ V)) (hf : IsCauchyFilter f) (hB : ∃ B ∈ f, Bornology.IsVonNBounded ℂ B) :
    ∃ (m : ℕ) (g : Filter (X m ⧸ V.comap (X m).subtype)), IsCauchyFilter g ∧
      ∀ G ∈ nhds (0 : E ⧸ V), ∃ A ∈ f, ∃ C ∈ g, ∀ a ∈ A, ∀ c ∈ C,
        a - Submodule.mapQ (V.comap (X m).subtype) V (X m).subtype le_rfl c ∈ G := by
  -- TVS structure on E
  obtain ⟨⟨⟨ι, _, p, hp⟩, _⟩, _⟩ :=
    strictLF_hlcs_and_closed_steps E X hmono hexh (fun n => (hX n).1) htop
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  obtain ⟨B, hBf, hBb⟩ := hB
  obtain ⟨n, A, hAb, hBA⟩ :=
    strictLF_quotient_regular_of_condM_of_localization E X hmono hexh hX htop V hV hL B hBb
  obtain ⟨B', hB'b, hAB'⟩ :=
    nuclear_frechet_quotient_lifts_bounded (X n) (hX n).1 (hX n).2 (V.comap (X n).subtype)
      (hV.preimage continuous_subtype_val) A hAb
  set q : E → E ⧸ V := Submodule.Quotient.mk with hq
  have hBimg : B ⊆ (fun x : X n => q (x : E)) '' B' := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := hBA hb
    obtain ⟨x, hx, rfl⟩ := hAB' ha
    exact ⟨x, hx, rfl⟩
  obtain ⟨m, hnm, U, hU, hUL⟩ := hL n
  -- scaling constant
  have hsub : Bornology.IsVonNBounded ℂ (B' - B') := hB'b.sub hB'b
  obtain ⟨a, haU, ha0⟩ :=
    ((hsub hU).and (Bornology.eventually_ne_cobounded (0 : ℂ))).exists
  have hscale : ∀ x ∈ B', ∀ y ∈ B', a⁻¹ • (x - y) ∈ U := by
    intro x hx y hy
    obtain ⟨u, hu, hxy⟩ := haU (Set.sub_mem_sub hx hy)
    rw [← hxy, smul_smul, inv_mul_cancel₀ ha0, one_smul]
    exact hu
  set ι' : X n → X m := fun x => Submodule.inclusion (hmono hnm) x
  set π : X m → X m ⧸ V.comap (X m).subtype := Submodule.Quotient.mk
  set h : Filter (X n) := Filter.comap (fun x : X n => q (x : E)) f ⊓ Filter.principal B'
  have : f.NeBot := hf.1
  have hh : h.NeBot := Filter.comap_inf_principal_neBot_of_image_mem hf.1
    (Filter.mem_of_superset hBf hBimg)
  refine ⟨m, Filter.map (fun x => π (ι' x)) h, ⟨Filter.map_neBot, ?_⟩, ?_⟩
  · intro W' hW'
    have hW0 : π ⁻¹' W' ∈ nhds (0 : X m) :=
      (continuous_quot_mk.tendsto (0 : X m)) hW'
    have hW : (fun w : X m => a • w) ⁻¹' (π ⁻¹' W') ∈ nhds (0 : X m) := by
      have := ((continuous_const_smul a).tendsto (0 : X m))
      rw [smul_zero] at this
      exact this hW0
    obtain ⟨G, hG, hGL⟩ := hUL _ hW
    have hG' : (fun z : E ⧸ V => a⁻¹ • z) ⁻¹' G ∈ nhds (0 : E ⧸ V) := by
      have := ((continuous_const_smul a⁻¹).tendsto (0 : E ⧸ V))
      rw [smul_zero] at this
      exact this hG
    obtain ⟨A0, hA0, hA0G⟩ := hf.2 _ hG'
    refine ⟨(fun x => π (ι' x)) '' ((fun x : X n => q (x : E)) ⁻¹' A0 ∩ B'),
      Filter.image_mem_map (Filter.inter_mem_inf (Filter.preimage_mem_comap hA0)
        (Filter.mem_principal_self B')), ?_⟩
    rintro _ ⟨x, ⟨hxA, hxB⟩, rfl⟩ _ ⟨y, ⟨hyA, hyB⟩, rfl⟩
    have hz := hscale x hxB y hyB
    have hqz : q ((a⁻¹ • (x - y) : X n) : E) ∈ G := by
      have := hA0G _ hxA _ hyA
      simpa [hq, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul] using this
    obtain ⟨w, hwW, hwV⟩ := hGL _ hz hqz
    have key : π (ι' x) - π (ι' y) = π (a • w) := by
      rw [← Submodule.Quotient.mk_sub]
      apply (Submodule.Quotient.eq _).2
      show ((ι' x - ι' y - a • w : X m) : E) ∈ V
      have : ((ι' x - ι' y - a • w : X m) : E) = a • (((a⁻¹ • (x - y) : X n) : E) - (w : E)) := by
        simp only [ι', Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_inclusion, smul_sub,
          smul_smul, mul_inv_cancel₀ ha0, one_smul]
      rw [this]
      exact V.smul_mem a hwV
    rw [key]
    exact hwW
  · intro G hG
    obtain ⟨A0, hA0, hA0G⟩ := hf.2 _ hG
    refine ⟨A0, hA0, (fun x => π (ι' x)) '' ((fun x : X n => q (x : E)) ⁻¹' A0 ∩ B'),
      Filter.image_mem_map (Filter.inter_mem_inf (Filter.preimage_mem_comap hA0)
        (Filter.mem_principal_self B')), ?_⟩
    rintro b hb _ ⟨x, ⟨hxA, _⟩, rfl⟩
    exact hA0G b hb _ hxA
