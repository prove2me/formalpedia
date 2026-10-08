-- Prove2me | solution 1 for MechanismDesign.IncentiveCompat.revenue_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T06:17:38.763981+00:00
-- url     : https://prove2.me/submissions/0317af67-6e09-4071-be8a-41da1da9157b

import Definitions.Def_MechanismDesign_IncentiveCompat_Model
set_option autoImplicit false

set_option autoImplicit false
namespace RochetCommonSupport

/-- Finite partition estimate for two functions sharing supporting slopes. -/
theorem partition_difference_bound (f g p : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, f x + p x * (y - x) ≤ f y)
    (hg : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, g x + p x * (y - x) ≤ g y)
    (N : ℕ) (hN : 0 < N) :
    (g b - g a) - (f b - f a) ≤ (b - a) / N * (p b - p a) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let δ : ℝ := (b - a) / N
  let mesh : ℕ → ℝ := fun k => a + δ * k
  have hδ : 0 ≤ δ := div_nonneg (sub_nonneg.mpr hab) hNr.le
  have hlast : mesh N = b := by
    dsimp [mesh, δ]
    field_simp
    ring
  have hmem : ∀ k, k ≤ N → mesh k ∈ Set.Icc a b := by
    intro k hk
    have hkr : (k : ℝ) ≤ N := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hprod := mul_le_mul_of_nonneg_left hkr hδ
    constructor
    · dsimp [mesh]
      nlinarith [mul_nonneg hδ hk0]
    · rw [← hlast]
      dsimp [mesh]
      linarith
  have hstep : ∀ k, mesh (k + 1) - mesh k = δ := by
    intro k
    simp only [mesh, Nat.cast_add, Nat.cast_one]
    ring
  have estimate : ∀ k, k ≤ N →
      g (mesh k) - f (mesh k) ≤ g a - f a + δ * (p (mesh k) - p a) := by
    intro k
    induction k with
    | zero => intro _; simp [mesh]
    | succ k ih =>
      intro hk
      have hk' : k ≤ N := by omega
      have hold := ih hk'
      have hleft := hf (mesh k) (hmem k hk') (mesh (k + 1)) (hmem (k + 1) hk)
      have hright := hg (mesh (k + 1)) (hmem (k + 1) hk) (mesh k) (hmem k hk')
      rw [hstep] at hleft
      have hrev : mesh k - mesh (k + 1) = -δ := by linarith [hstep k]
      rw [hrev] at hright
      nlinarith
  have h := estimate N le_rfl
  rw [hlast] at h
  dsimp [δ] at h
  linarith

/-- A common supporting slope at every point forces identical increments.
The proof uses finite partitions and the Archimedean property, without an
assumption of differentiability or integrability. -/
theorem increments_eq_of_common_support (f g p : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, f x + p x * (y - x) ≤ f y)
    (hg : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, g x + p x * (y - x) ≤ g y) :
    f b - f a = g b - g a := by
  have one_side : ∀ (F G : ℝ → ℝ),
      (∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, F x + p x * (y - x) ≤ F y) →
      (∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, G x + p x * (y - x) ≤ G y) →
      (G b - G a) - (F b - F a) ≤ 0 := by
    intro F G hF hG
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (((b - a) * (p b - p a)) / ε)
    have hden : (0 : ℝ) < (N + 1 : ℕ) := by positivity
    have hgt : ((b - a) * (p b - p a)) / ε < (N + 1 : ℕ) := by
      exact hN.trans (by push_cast; linarith)
    have hprod : (b - a) * (p b - p a) < ((N + 1 : ℕ) : ℝ) * ε :=
      (div_lt_iff₀ hε).mp hgt
    have hfrac : (b - a) / (N + 1 : ℕ) * (p b - p a) < ε := by
      have h : ((b - a) * (p b - p a)) / ((N + 1 : ℕ) : ℝ) < ε :=
        (div_lt_iff₀ hden).mpr (by simpa [mul_comm] using hprod)
      simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
    have hbound := partition_difference_bound F G p a b hab hF hG (N + 1) (by omega)
    simpa only [zero_add] using hbound.trans hfrac.le
  have hfg := one_side f g hf hg
  have hgf := one_side g f hg hf
  linarith

/-- The right derivative of a convex function supports it on either side of
an interior point; the function need not have an ordinary derivative there. -/
theorem convex_right_support {S : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ S f)
    {x : ℝ} (hx : x ∈ interior S) :
    ∀ y ∈ S, f x + derivWithin f (Set.Ioi x) x * (y - x) ≤ f y := by
  intro y hy
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · have h := hf.rightDeriv_le_slope_of_mem_interior hx hy hxy
    rw [slope_def_field] at h
    have hm := (le_div_iff₀ (sub_pos.mpr hxy)).mp h
    linarith
  · subst y
    simp
  · have h := (hf.slope_le_leftDeriv_of_mem_interior hy hx hyx).trans
      (hf.leftDeriv_le_rightDeriv_of_mem_interior hx)
    rw [slope_def_field] at h
    have hm := (div_le_iff₀ (sub_pos.mpr hyx)).mp h
    nlinarith

end RochetCommonSupport

set_option autoImplicit false
namespace RochetRevenue
open MechanismDesign.IncentiveCompat

/-- IC makes truthful utility convex whenever every allocation's utility is
convex. The ambient extension is constrained only on the actual type set. -/
theorem truthful_utility_convex {A E : Type*} [AddCommGroup E] [Module ℝ E]
    (S : Set E) (hS : Convex ℝ S) (w : A → E → ℝ)
    (hconv : ∀ a, ConvexOn ℝ S (w a)) (q : S → A) (t : S → ℝ)
    (hIC : IsIC (fun (a : A) (θ : S) => w a (θ : E)) ⟨q, t⟩)
    (F : E → ℝ) (hF : ∀ θ : S, F θ = w (q θ) θ - t θ) : ConvexOn ℝ S F := by
  refine ⟨hS, ?_⟩
  intro x hx y hy α β hα hβ hsum
  let z : E := α • x + β • y
  have hz : z ∈ S := hS hx hy hα hβ hsum
  let θz : S := ⟨z, hz⟩
  let θx : S := ⟨x, hx⟩
  let θy : S := ⟨y, hy⟩
  have halloc := (hconv (q θz)).2 hx hy hα hβ hsum
  have hix := hIC θx θz
  have hiy := hIC θy θz
  change w (q θz) x - t θz ≤ w (q θx) x - t θx at hix
  change w (q θz) y - t θz ≤ w (q θy) y - t θy at hiy
  have hix' := mul_le_mul_of_nonneg_left hix hα
  have hiy' := mul_le_mul_of_nonneg_left hiy hβ
  have hprice := congrArg (fun c : ℝ => c * t θz) hsum
  change F z ≤ α * F x + β * F y
  have hfz := hF θz
  have hfx := hF θx
  have hfy := hF θy
  change F z = w (q θz) z - t θz at hfz
  change F x = w (q θx) x - t θx at hfx
  change F y = w (q θy) y - t θy at hfy
  change w (q θz) z ≤ α * w (q θz) x + β * w (q θz) y at halloc
  nlinarith

end RochetRevenue

set_option autoImplicit false
namespace RochetRevenue
open MechanismDesign.IncentiveCompat

/-- The allocated utility's right derivative supports the truthful potential
at an interior type, with no differentiability premise on that allocation. -/
theorem truthful_right_support {A : Type*} (S : Set ℝ) (w : A → ℝ → ℝ)
    (hconv : ∀ a, ConvexOn ℝ S (w a)) (q : S → A) (t : S → ℝ)
    (hIC : IsIC (fun (a : A) (θ : S) => w a (θ : ℝ)) ⟨q, t⟩)
    (F : ℝ → ℝ) (hF : ∀ θ : S, F θ = w (q θ) θ - t θ)
    (x : ℝ) (hx : x ∈ interior S) :
    ∀ y ∈ S, F x + derivWithin (w (q ⟨x, interior_subset hx⟩)) (Set.Ioi x) x *
      (y - x) ≤ F y := by
  intro y hy
  let θx : S := ⟨x, interior_subset hx⟩
  let θy : S := ⟨y, hy⟩
  have hs := RochetCommonSupport.convex_right_support (hconv (q θx)) hx y hy
  have hic := hIC θy θx
  change w (q θx) y - t θx ≤ w (q θy) y - t θy at hic
  have hfx := hF θx
  have hfy := hF θy
  change F x = w (q θx) x - t θx at hfx
  change F y = w (q θy) y - t θy at hfy
  change F x + derivWithin (w (q θx)) (Set.Ioi x) x * (y - x) ≤ F y
  linarith

/-- Revenue differences agree across every compact interval in the interior
of a one-dimensional convex type domain. Endpoint passage is still separate. -/
theorem interior_payment_difference {A : Type*} (S : Set ℝ) (w : A → ℝ → ℝ)
    (hconv : ∀ a, ConvexOn ℝ S (w a)) (q : S → A) (t t' : S → ℝ)
    (hIC : IsIC (fun (a : A) (θ : S) => w a (θ : ℝ)) ⟨q, t⟩)
    (hIC' : IsIC (fun (a : A) (θ : S) => w a (θ : ℝ)) ⟨q, t'⟩)
    (a b : ℝ) (hab : a ≤ b) (hinterval : Set.Icc a b ⊆ interior S) :
    t' ⟨a, interior_subset (hinterval ⟨le_rfl, hab⟩)⟩ -
      t ⟨a, interior_subset (hinterval ⟨le_rfl, hab⟩)⟩ =
    t' ⟨b, interior_subset (hinterval ⟨hab, le_rfl⟩)⟩ -
      t ⟨b, interior_subset (hinterval ⟨hab, le_rfl⟩)⟩ := by
  classical
  let F : ℝ → ℝ := fun x => if hx : x ∈ S then w (q ⟨x, hx⟩) x - t ⟨x, hx⟩ else 0
  let G : ℝ → ℝ := fun x => if hx : x ∈ S then w (q ⟨x, hx⟩) x - t' ⟨x, hx⟩ else 0
  let p : ℝ → ℝ := fun x => if hx : x ∈ S then
    derivWithin (w (q ⟨x, hx⟩)) (Set.Ioi x) x else 0
  have hF : ∀ θ : S, F θ = w (q θ) θ - t θ := by intro θ; simp [F, θ.property]
  have hG : ∀ θ : S, G θ = w (q θ) θ - t' θ := by intro θ; simp [G, θ.property]
  have support : ∀ (U : ℝ → ℝ) (T : S → ℝ),
      IsIC (fun (a : A) (θ : S) => w a (θ : ℝ)) ⟨q, T⟩ →
      (∀ θ : S, U θ = w (q θ) θ - T θ) →
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, U x + p x * (y - x) ≤ U y := by
    intro U T hic hu x hx y hy
    have hxs : x ∈ S := interior_subset (hinterval hx)
    have hys : y ∈ S := interior_subset (hinterval hy)
    simpa only [p, dif_pos hxs] using
      truthful_right_support S w hconv q T hic U hu x (hinterval hx) y hys
  have heq := RochetCommonSupport.increments_eq_of_common_support F G p a b hab
    (support F t hIC hF) (support G t' hIC' hG)
  have ha : a ∈ S := interior_subset (hinterval ⟨le_rfl, hab⟩)
  have hb : b ∈ S := interior_subset (hinterval ⟨hab, le_rfl⟩)
  simp only [F, G, dif_pos ha, dif_pos hb] at heq
  linarith

end RochetRevenue

set_option autoImplicit false
namespace RochetRevenue
open MechanismDesign.IncentiveCompat

/-- Convexity gives a chord upper bound; continuous touching functions give
the lower bounds at both endpoints. Interior continuity then fills the interval. -/
theorem convex_touching_continuous (F g₀ g₁ : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Icc 0 1) F)
    (hg₀ : ContinuousWithinAt g₀ (Set.Icc 0 1) 0)
    (hg₁ : ContinuousWithinAt g₁ (Set.Icc 0 1) 1)
    (hle₀ : ∀ x ∈ Set.Icc 0 1, g₀ x ≤ F x)
    (hle₁ : ∀ x ∈ Set.Icc 0 1, g₁ x ≤ F x)
    (heq₀ : g₀ 0 = F 0) (heq₁ : g₁ 1 = F 1) :
    ContinuousOn F (Set.Icc 0 1) := by
  let chord : ℝ → ℝ := fun x => (1 - x) * F 0 + x * F 1
  have hupper : ∀ x ∈ Set.Icc 0 1, F x ≤ chord x := by
    intro x hx
    have h := hf.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
      (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)
      (show 0 ≤ 1 - x by linarith [hx.2]) hx.1 (by ring)
    simpa [chord] using h
  have endpoint (z : ℝ) (hz : z = 0 ∨ z = 1) (g : ℝ → ℝ)
      (hg : ContinuousWithinAt g (Set.Icc 0 1) z)
      (hle : ∀ x ∈ Set.Icc 0 1, g x ≤ F x) (heq : g z = F z) :
      ContinuousWithinAt F (Set.Icc 0 1) z := by
    have hc : ContinuousWithinAt chord (Set.Icc 0 1) z := by
      dsimp [chord]
      fun_prop
    have hchord : chord z = F z := by rcases hz with rfl | rfl <;> simp [chord]
    change Filter.Tendsto F (nhdsWithin z (Set.Icc 0 1)) (nhds (F z))
    have hlow : Filter.Tendsto g (nhdsWithin z (Set.Icc 0 1)) (nhds (F z)) := by
      change Filter.Tendsto g (nhdsWithin z (Set.Icc 0 1)) (nhds (g z)) at hg
      simpa only [heq] using hg
    have hup : Filter.Tendsto chord (nhdsWithin z (Set.Icc 0 1)) (nhds (F z)) := by
      change Filter.Tendsto chord (nhdsWithin z (Set.Icc 0 1)) (nhds (chord z)) at hc
      simpa only [hchord] using hc
    apply hlow.squeeze' hup
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact hle x hx
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact hupper x hx
  intro x hx
  by_cases hx₀ : x = 0
  · subst x
    exact endpoint 0 (Or.inl rfl) g₀ hg₀ hle₀ heq₀
  by_cases hx₁ : x = 1
  · subst x
    exact endpoint 1 (Or.inr rfl) g₁ hg₁ hle₁ heq₁
  have hxi : x ∈ interior (Set.Icc (0 : ℝ) 1) := by
    rw [interior_Icc]
    exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hx₀), lt_of_le_of_ne hx.2 hx₁⟩
  have hc := hf.continuousOn_interior x hxi
  have hopen : interior (Set.Icc (0 : ℝ) 1) ∈ nhds x := isOpen_interior.mem_nhds hxi
  exact ((continuousWithinAt_iff_continuousAt hopen).mp hc).continuousWithinAt

end RochetRevenue

set_option autoImplicit false
namespace RochetRevenue
open MechanismDesign.IncentiveCompat

/-- Continuous allocated utilities prevent endpoint jumps in the truthful
potential. No continuity of the allocation or payment rule is assumed. -/
theorem truthful_utility_continuous {A : Type*} (w : A → ℝ → ℝ)
    (hconv : ∀ a, ConvexOn ℝ (Set.Icc 0 1) (w a))
    (hcont : ∀ a, ContinuousOn (w a) (Set.Icc 0 1))
    (q : Set.Icc (0 : ℝ) 1 → A) (t : Set.Icc (0 : ℝ) 1 → ℝ)
    (hIC : IsIC (fun (a : A) (θ : Set.Icc (0 : ℝ) 1) => w a (θ : ℝ)) ⟨q, t⟩)
    (F : ℝ → ℝ) (hF : ∀ θ : Set.Icc (0 : ℝ) 1, F θ = w (q θ) θ - t θ) :
    ContinuousOn F (Set.Icc 0 1) := by
  let θ₀ : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let θ₁ : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  let g₀ : ℝ → ℝ := fun x => w (q θ₀) x - t θ₀
  let g₁ : ℝ → ℝ := fun x => w (q θ₁) x - t θ₁
  apply convex_touching_continuous F g₀ g₁
    (truthful_utility_convex (Set.Icc 0 1) (convex_Icc 0 1) w hconv q t hIC F hF)
  · exact (hcont (q θ₀) 0 (by norm_num)).sub continuousWithinAt_const
  · exact (hcont (q θ₁) 1 (by norm_num)).sub continuousWithinAt_const
  · intro x hx
    have h := hIC ⟨x, hx⟩ θ₀
    have hf := hF ⟨x, hx⟩
    change w (q θ₀) x - t θ₀ ≤ w (q ⟨x, hx⟩) x - t ⟨x, hx⟩ at h
    exact h.trans_eq hf.symm
  · intro x hx
    have h := hIC ⟨x, hx⟩ θ₁
    have hf := hF ⟨x, hx⟩
    change w (q θ₁) x - t θ₁ ≤ w (q ⟨x, hx⟩) x - t ⟨x, hx⟩ at h
    exact h.trans_eq hf.symm
  · exact (hF θ₀).symm
  · exact (hF θ₁).symm

end RochetRevenue

set_option autoImplicit false
namespace RochetRevenue
open MechanismDesign.IncentiveCompat

/-- The difference of two IC payment rules agrees at the endpoints of the
unit interval. Continuity is used through fixed endpoint allocations. -/
theorem payment_difference_endpoints {A : Type*} (w : A → ℝ → ℝ)
    (hconv : ∀ a, ConvexOn ℝ (Set.Icc 0 1) (w a))
    (hcont : ∀ a, ContinuousOn (w a) (Set.Icc 0 1))
    (q : Set.Icc (0 : ℝ) 1 → A) (t t' : Set.Icc (0 : ℝ) 1 → ℝ)
    (hIC : IsIC (fun (a : A) (θ : Set.Icc (0 : ℝ) 1) => w a (θ : ℝ)) ⟨q, t⟩)
    (hIC' : IsIC (fun (a : A) (θ : Set.Icc (0 : ℝ) 1) => w a (θ : ℝ)) ⟨q, t'⟩) :
    t' ⟨0, by norm_num⟩ - t ⟨0, by norm_num⟩ =
      t' ⟨1, by norm_num⟩ - t ⟨1, by norm_num⟩ := by
  classical
  let F : ℝ → ℝ := fun x => if hx : x ∈ Set.Icc (0 : ℝ) 1 then
    w (q ⟨x, hx⟩) x - t ⟨x, hx⟩ else 0
  let G : ℝ → ℝ := fun x => if hx : x ∈ Set.Icc (0 : ℝ) 1 then
    w (q ⟨x, hx⟩) x - t' ⟨x, hx⟩ else 0
  let H : ℝ → ℝ := fun x => F x - G x
  have hF : ∀ θ : Set.Icc (0 : ℝ) 1, F θ = w (q θ) θ - t θ := by
    intro θ; simp only [F, dif_pos θ.property]
  have hG : ∀ θ : Set.Icc (0 : ℝ) 1, G θ = w (q θ) θ - t' θ := by
    intro θ; simp only [G, dif_pos θ.property]
  have hcF := truthful_utility_continuous w hconv hcont q t hIC F hF
  have hcG := truthful_utility_continuous w hconv hcont q t' hIC' G hG
  have hcH : ContinuousOn H (Set.Icc 0 1) := hcF.sub hcG
  have heq : Set.EqOn H (fun _ => H (1 / 2)) (Set.Ioo (0 : ℝ) 1) := by
    intro x hx
    have hxS : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    have hhS : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := by norm_num
    rcases le_total x (1 / 2) with hxh | hhx
    · have hi : Set.Icc x (1 / 2 : ℝ) ⊆ interior (Set.Icc (0 : ℝ) 1) := by
        rw [interior_Icc]
        intro z hz
        constructor <;> linarith [hx.1, hx.2, hz.1, hz.2]
      have hd := interior_payment_difference (Set.Icc 0 1) w hconv q t t' hIC hIC'
        x (1 / 2) hxh hi
      dsimp [H]
      simp only [F, G, dif_pos hxS, dif_pos hhS]
      linarith
    · have hi : Set.Icc (1 / 2 : ℝ) x ⊆ interior (Set.Icc (0 : ℝ) 1) := by
        rw [interior_Icc]
        intro z hz
        constructor <;> linarith [hx.1, hx.2, hz.1, hz.2]
      have hd := interior_payment_difference (Set.Icc 0 1) w hconv q t t' hIC hIC'
        (1 / 2) x hhx hi
      dsimp [H]
      simp only [F, G, dif_pos hxS, dif_pos hhS]
      linarith
  have hext : Set.EqOn H (fun _ => H (1 / 2)) (Set.Icc (0 : ℝ) 1) :=
    heq.of_subset_closure hcH continuousOn_const Set.Ioo_subset_Icc_self (by
      rw [closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)])
  have hz : H 0 = H (1 / 2) := hext (by norm_num)
  have ho : H 1 = H (1 / 2) := hext (by norm_num)
  simp only [H, F, G, dif_pos (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num),
    dif_pos (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)] at hz ho
  linarith

end RochetRevenue

set_option autoImplicit false
namespace RochetRevenue
open MechanismDesign.IncentiveCompat

/-- Pull back the mechanism to a segment between arbitrary original types. -/
theorem payment_difference_pair {A : Type*} {n : ℕ}
    (S : Set (Fin n → ℝ)) (hS : Convex ℝ S)
    (w : A → (Fin n → ℝ) → ℝ) (hconv : ∀ a, ConvexOn ℝ S (w a))
    (hcont : ∀ a, ContinuousOn (w a) S) (q : S → A) (t t' : S → ℝ)
    (hIC : IsIC (fun (a : A) (θ : S) => w a (θ : Fin n → ℝ)) ⟨q, t⟩)
    (hIC' : IsIC (fun (a : A) (θ : S) => w a (θ : Fin n → ℝ)) ⟨q, t'⟩)
    (x y : S) : t' x - t x = t' y - t y := by
  let seg : ℝ → (Fin n → ℝ) := fun r => (1 - r) • (x : Fin n → ℝ) + r • y
  have hmem : ∀ r ∈ Set.Icc (0 : ℝ) 1, seg r ∈ S := by
    intro r hr
    exact hS x.property y.property (by linarith [hr.2]) hr.1 (by ring)
  let pull : Set.Icc (0 : ℝ) 1 → S := fun r => ⟨seg r, hmem r r.property⟩
  let v : A → ℝ → ℝ := fun a r => w a (seg r)
  let Q : Set.Icc (0 : ℝ) 1 → A := fun r => q (pull r)
  let T : Set.Icc (0 : ℝ) 1 → ℝ := fun r => t (pull r)
  let T' : Set.Icc (0 : ℝ) 1 → ℝ := fun r => t' (pull r)
  have haff : ∀ r s α β : ℝ, α + β = 1 →
      seg (α * r + β * s) = α • seg r + β • seg s := by
    intro r s α β hsum
    ext i
    simp only [seg, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hbase := congrArg (fun c : ℝ => c * x.val i) hsum
    nlinarith
  have hvconv : ∀ a, ConvexOn ℝ (Set.Icc 0 1) (v a) := by
    intro a
    refine ⟨convex_Icc 0 1, ?_⟩
    intro r hr s hs α β hα hβ hsum
    change w a (seg (α * r + β * s)) ≤ α * w a (seg r) + β * w a (seg s)
    rw [haff r s α β hsum]
    exact (hconv a).2 (hmem r hr) (hmem s hs) hα hβ hsum
  have hvcont : ∀ a, ContinuousOn (v a) (Set.Icc 0 1) := by
    intro a
    have hc : Continuous seg := by dsimp [seg]; fun_prop
    exact (hcont a).comp hc.continuousOn hmem
  have hic : IsIC (fun (a : A) (r : Set.Icc (0 : ℝ) 1) => v a (r : ℝ)) ⟨Q, T⟩ := by
    intro r s
    exact hIC (pull r) (pull s)
  have hic' : IsIC (fun (a : A) (r : Set.Icc (0 : ℝ) 1) => v a (r : ℝ)) ⟨Q, T'⟩ := by
    intro r s
    exact hIC' (pull r) (pull s)
  have hzero : pull ⟨0, by norm_num⟩ = x := by
    apply Subtype.ext
    simp [pull, seg]
  have hone : pull ⟨1, by norm_num⟩ = y := by
    apply Subtype.ext
    simp [pull, seg]
  have h := payment_difference_endpoints v hvconv hvcont Q T T' hic hic'
  simpa only [T, T', hzero, hone] using h

end RochetRevenue
open MechanismDesign.IncentiveCompat
theorem solution {A : Type*} {n : ℕ} (S : Set (Fin n → ℝ)) (hS : Convex ℝ S)
    (hSne : S.Nonempty) (w : A → (Fin n → ℝ) → ℝ) (hconv : ∀ a, ConvexOn ℝ S (w a))
    (hcont : ∀ a, ContinuousOn (w a) S) (q : S → A) (t : S → ℝ)
    (hIC : IsIC (fun (a : A) (θ : S) => w a (θ : Fin n → ℝ)) ⟨q, t⟩) (t' : S → ℝ) :
    IsIC (fun (a : A) (θ : S) => w a (θ : Fin n → ℝ)) ⟨q, t'⟩ ↔
      ∃ τ : ℝ, ∀ θ : S, t' θ = t θ + τ := by
  constructor
  · intro hic'
    obtain ⟨x, hx⟩ := hSne
    let θ₀ : S := ⟨x, hx⟩
    refine ⟨t' θ₀ - t θ₀, ?_⟩
    intro θ
    have h := RochetRevenue.payment_difference_pair S hS w hconv hcont q t t' hIC hic' θ₀ θ
    linarith
  · rintro ⟨τ, ht⟩
    intro θ η
    have h := hIC θ η
    change w (q η) θ - t' η ≤ w (q θ) θ - t' θ
    rw [ht η, ht θ]
    dsimp [IsIC] at h
    linarith

#print axioms solution
