-- Prove2me | solution 1 for MasulloRH.two_residue_theta_graph_quotient_and_translation_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T08:19:26.475366+00:00
-- url     : https://prove2.me/submissions/20f81f62-a6c2-4e45-adcd-eb8011148e37

import Mathlib
open Set
theorem solution {S H K : Type*} [AddCommGroup S] [Module ℂ S]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup K] [NormedSpace ℂ K]
    (r : S →ₗ[ℂ] ℂ × ℂ) (hr : Function.Surjective r)
    (Y : S →ₗ[ℂ] H) (q : H →L[ℂ] K) (hq : Function.Surjective q)
    (hcore : closure (Y '' (r.ker : Set S)) = (q.ker : Set H)) :
    ∃ F : (ℂ × ℂ) → K, Continuous F ∧ (∀ h : S, q (Y h) = F (r h)) ∧
      Function.Surjective (fun p : H × (ℂ × ℂ) => q p.1 - F p.2) ∧
      closure (Set.range fun h : S => (Y h, r h)) =
        {p : H × (ℂ × ℂ) | q p.1 - F p.2 = 0} ∧
      ∀ (U : H →ₗ[ℂ] H) (V : K →ₗ[ℂ] K) (D : (ℂ × ℂ) →ₗ[ℂ] ℂ × ℂ)
        (T : S →ₗ[ℂ] S) (C : (ℂ × ℂ) →ₗ[ℂ] H),
        (∀ x, q (U x) = V (q x)) → (∀ h, r (T h) = D (r h)) →
        (∀ h, Y (T h) = U (Y h) + C (r h)) →
        (∀ b, q (C b) = F (D b) - V (F b)) ∧
        (∀ x b, q (U x + C b) - F (D b) = V (q x - F b)) := by
  classical
  obtain ⟨a,ha⟩ := hr (1,0)
  obtain ⟨b,hb⟩ := hr (0,1)
  let lift := fun z : ℂ × ℂ => z.1 • a + z.2 • b
  have hLift (z : ℂ × ℂ) : r (lift z) = z := by
    ext <;> simp [lift,ha,hb]
  let F := fun z : ℂ × ℂ => q (Y (lift z))
  have hFc : Continuous F := by
    simp only [F,lift,map_add,map_smul]
    fun_prop
  have h0 (h : S) (hh : r h = 0) : q (Y h) = 0 := by
    change Y h ∈ (q.ker : Set H)
    rw [← hcore]
    exact subset_closure ⟨h, hh, rfl⟩
  have hF (h : S) : q (Y h) = F (r h) := by
    have hh := h0 (h-lift (r h)) (by simp [hLift])
    simpa only [map_sub,sub_eq_zero,F] using hh
  refine ⟨F,hFc,hF,?_,?_,?_⟩
  · intro z
    obtain ⟨x,hx⟩ := hq z
    exact ⟨(x,0),by simp [F,lift,hx]⟩
  · apply le_antisymm
    · apply closure_minimal
      · rintro z ⟨h,rfl⟩
        exact sub_eq_zero.mpr (hF h)
      · exact isClosed_eq ((q.continuous.comp continuous_fst).sub (hFc.comp continuous_snd)) continuous_const
    · rintro ⟨x,z⟩ h
      change q x - F z = 0 at h
      have hm : x-Y (lift z) ∈ closure (Y '' (r.ker : Set S)) := by
        rw [hcore]
        change q (x-Y (lift z)) = 0
        simpa only [map_sub,F] using h
      let f := fun y : H => (y+Y (lift z),z)
      have hc : Continuous f := by dsimp [f]; fun_prop
      have him : f '' (Y '' (r.ker : Set S)) ⊆ Set.range (fun h : S => (Y h,r h)) := by
        rintro v ⟨_,⟨s,hs,rfl⟩,rfl⟩
        change r s = 0 at hs
        exact ⟨s+lift z,by simp [f,hLift,hs]⟩
      have hv : f (x-Y (lift z)) ∈ closure (f '' (Y '' (r.ker : Set S))) :=
        image_closure_subset_closure_image hc ⟨_,hm,rfl⟩
      simpa only [f,sub_add_cancel] using closure_mono him hv
  · intro U V D T C hU hT hY
    have hC (z : ℂ × ℂ) : q (C z) = F (D z) - V (F z) := by
      have ht := hF (T (lift z))
      rw [hY,map_add,hU,hT,hLift] at ht
      change V (F z) + q (C z) = F (D z) at ht
      exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using ht)
    refine ⟨hC,?_⟩
    intro x z
    rw [map_add,hU,hC,map_sub]
    abel
