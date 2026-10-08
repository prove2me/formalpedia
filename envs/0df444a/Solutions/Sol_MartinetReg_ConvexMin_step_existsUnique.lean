-- Prove2me | solution 1 for MartinetReg.ConvexMin.step_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:11:45.435246+00:00
-- url     : https://prove2.me/submissions/0bff82c3-cb9d-4603-90bb-81cf38d09955

import Definitions.Def_MartinetReg_ConvexMin_Setting
open MartinetReg.ConvexMin
open Set Topology

private theorem weak_closed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {S : Set H} (hS : Convex ℝ S) (hc : IsClosed S) :
    IsClosed (toWeakSpace ℝ H '' S) := by
  have he := hS.toWeakSpace_closure ℝ
  rw [hc.closure_eq] at he
  exact closure_eq_iff_isClosed.mp he.symm

private theorem weak_compact {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {S : Set H} (hS : Convex ℝ S) (hc : IsClosed S)
    (hb : Bornology.IsBounded S) : IsCompact (toWeakSpace ℝ H '' S) := by
  have hsur : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ H) := by
    intro L
    let e := InnerProductSpace.toDual ℝ H
    let f : StrongDual ℝ H := L.comp e.toContinuousLinearEquiv.toContinuousLinearMap
    refine ⟨e.symm f, ?_⟩
    ext g
    have hg : e (e.symm g) = g := e.apply_symm_apply g
    change g (e.symm f) = L g
    rw [← hg]
    change inner ℝ (e.symm g) (e.symm f) = L (e (e.symm g))
    rw [real_inner_comm]
    change e (e.symm f) (e.symm g) = L (e (e.symm g))
    rw [e.apply_symm_apply]
    rfl
  have hsurw : Function.Surjective (NormedSpace.inclusionInDoubleDualWeak ℝ H) := by
    intro L
    obtain ⟨x, hx⟩ := hsur (StrongDual.toWeakDual.symm L)
    refine ⟨toWeakSpace ℝ H x, ?_⟩
    apply StrongDual.toWeakDual.symm.injective
    exact hx
  have hn := NormedSpace.isCompact_closure_of_isBounded ℝ H (toWeakSpace ℝ H '' S)
    (by rw [Set.preimage_image_eq _ (toWeakSpace ℝ H).injective]; exact hb)
    (by rw [Set.range_eq_univ.mpr hsurw]; exact Set.subset_univ _)
  rwa [(weak_closed hS hc).closure_eq] at hn

private theorem convex_min_exists {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (C : Set H) (hS : Standing f C) :
    ∃ xs ∈ C, ∀ x ∈ C, f xs ≤ f x := by
  let e := toWeakSpace ℝ H
  have hf : LowerSemicontinuous (fun x : WeakSpace ℝ H => f (e.symm x)) := by
    apply lowerSemicontinuous_iff_isClosed_preimage.mpr
    intro a
    have he : (fun x : WeakSpace ℝ H => f (e.symm x)) ⁻¹' Iic a =
        e '' {x : H | f x ≤ a} := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_image, mem_setOf_eq]
      constructor
      · intro hx; exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
      · rintro ⟨y, hy, rfl⟩; simpa using hy
    rw [he]
    exact weak_closed (by simpa using hS.fconvex.convex_le a) (hS.flsc.isClosed_preimage a)
  obtain ⟨x0, hx0⟩ := hS.nonempty
  let K := {x : H | x ∈ C ∧ f x ≤ f x0}
  have hsubconv : Convex ℝ {x : H | f x ≤ f x0} := by
    simpa using hS.fconvex.convex_le (f x0)
  have hKconv : Convex ℝ K := hS.convex.inter hsubconv
  have hKclosed : IsClosed K := hS.closed.inter (hS.flsc.isClosed_preimage (f x0))
  have hKcomp := weak_compact hKconv hKclosed (hS.sublevel_bounded (f x0))
  obtain ⟨y, hy, hmy⟩ := LowerSemicontinuousOn.exists_isMinOn
    (Set.Nonempty.image e (show K.Nonempty from ⟨x0, hx0, le_rfl⟩)) hKcomp
    (hf.lowerSemicontinuousOn _)
  obtain ⟨xs, hxs, rfl⟩ := hy
  refine ⟨xs, hxs.1, ?_⟩
  intro x hx
  by_cases hfx : f x ≤ f x0
  · have hh := hmy (Set.mem_image_of_mem e (show x ∈ K from ⟨hx, hfx⟩))
    simpa using hh
  · exact hxs.2.trans (le_of_not_ge hfx)

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (C : Set H) (hS : Standing f C) :
    ∀ xn ∈ C, ∃! y : H, IsProxStep f C xn y := by
  intro xn hxn
  let g := fun x : H => f x + ‖x - xn‖ ^ 2
  have hsc : StrongConvexOn Set.univ 2 g := by
    refine ⟨convex_univ, ?_⟩
    intro x hx z hz a b ha hb hab
    have hc := hS.fconvex.2 hx hz ha hb hab
    have he : a • x + b • z - xn = a • (x - xn) + b • (z - xn) := by
      rw [smul_sub, smul_sub, ← add_sub_add_comm, ← add_smul, hab, one_smul]
    have he' : ‖a • (x - xn) + b • (z - xn)‖ ^ 2 =
        a * ‖x - xn‖ ^ 2 + b * ‖z - xn‖ ^ 2 - a * b * ‖x - z‖ ^ 2 := by
      have hd : x - z = (x - xn) - (z - xn) := by abel
      rw [hd]
      generalize x - xn = u
      generalize z - xn = v
      rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul,
        real_inner_smul_left, inner_smul_right, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      obtain rfl := eq_sub_of_add_eq hab
      ring
    simp only [g, smul_eq_mul, he, he']
    simp only [smul_eq_mul] at hc
    nlinarith
  have hgconv : ConvexOn ℝ Set.univ g := by
    exact strongConvexOn_zero.mp (hsc.mono (by norm_num))
  have hgcont : Continuous (fun x : H => ‖x - xn‖ ^ 2) := by fun_prop
  have hgStanding : Standing g C :=
    { convex := hS.convex
      closed := hS.closed
      nonempty := hS.nonempty
      fconvex := hgconv
      flsc := hS.flsc.add hgcont.lowerSemicontinuous
      sublevel_bounded := fun a => (hS.sublevel_bounded a).subset (by
        intro x hx
        exact ⟨hx.1, le_trans (by dsimp [g]; nlinarith [sq_nonneg ‖x - xn‖]) hx.2⟩) }
  obtain ⟨y, hy, hmy⟩ := convex_min_exists g C hgStanding
  refine ⟨y, ⟨hy, hmy⟩, ?_⟩
  intro z hz
  have hcsc : StrictConvexOn ℝ C g := (hsc.strictConvexOn (by norm_num)).subset
    (Set.subset_univ C) hS.convex
  exact hcsc.eq_of_isMinOn hz.2 hmy hz.1 hy

#print axioms solution
