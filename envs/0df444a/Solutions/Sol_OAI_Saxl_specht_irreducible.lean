-- Prove2me | solution 1 for OAI.Saxl.specht_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:23:05.174892+00:00
-- url     : https://prove2.me/submissions/174bf05b-4a4c-4c60-b37a-ddb6b8224466

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule

open OAI OAI.Saxl
open scoped TensorProduct
universe uG uV
theorem h42_finset_eq {X : Type*} [DecidableEq X]
    (A B : Finset X) (w : X → ℤ)
    (hp : ∀ x ∈ B, 0 < w x) (hn : ∀ x ∉ B, w x < 0)
    (he : ∑ x ∈ A, w x = ∑ x ∈ B, w x) : A = B := by
  have h1 := Finset.sum_sdiff (s₁ := A ∩ B) (s₂ := A) (f := w) Finset.inter_subset_left
  have h2 := Finset.sum_sdiff (s₁ := A ∩ B) (s₂ := B) (f := w) Finset.inter_subset_right
  have e1 : A \ (A ∩ B) = A \ B := by ext x; simp
  have e2 : B \ (A ∩ B) = B \ A := by ext x; simp [and_comm]
  rw [e1] at h1; rw [e2] at h2
  have hAB : ∑ x ∈ A \ B, w x = ∑ x ∈ B \ A, w x := by omega
  have hle : ∑ x ∈ A \ B, w x ≤ 0 := Finset.sum_nonpos (fun x hx => by
    have := hn x (Finset.mem_sdiff.1 hx).2; omega)
  have hge : 0 ≤ ∑ x ∈ B \ A, w x := Finset.sum_nonneg (fun x hx => by
    have := hp x (Finset.mem_sdiff.1 hx).1; omega)
  have d1 : A \ B = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have : ∑ x ∈ A \ B, w x < 0 := Finset.sum_neg (fun x hx => hn x (Finset.mem_sdiff.1 hx).2) ⟨y, hy⟩
    omega
  have d2 : B \ A = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have : 0 < ∑ x ∈ B \ A, w x := Finset.sum_pos (fun x hx => hp x (Finset.mem_sdiff.1 hx).1) ⟨y, hy⟩
    omega
  rw [Finset.sdiff_eq_empty_iff_subset] at d1 d2
  exact Finset.Subset.antisymm d1 d2

theorem h42_columnAlt_mul {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    columnAlt (d := d) t * wordRep n d (h : Equiv.Perm (Fin n)) =
      signC (h : Equiv.Perm (Fin n)) • columnAlt t := by
  classical
  let _ := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  rw [Finset.sum_mul, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun g => ?_)
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, map_mul, smul_smul, smul_mul_assoc]
  congr 1
  rw [mul_comm (signC (g : Equiv.Perm (Fin n))), ← mul_assoc, signC_mul_self, one_mul]

theorem h42_collision {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin d) (i j : Fin n) (hij : i ≠ j)
    (hc : (t i).val.2 = (t j).val.2) (ha : a i = a j) :
    columnAlt t (Pi.single a (1 : ℂ)) = 0 := by
  classical
  have hτ : Equiv.swap i j ∈ columnGroup t := by
    intro k
    rcases eq_or_ne k i with rfl | hki
    · simp [hc]
    rcases eq_or_ne k j with rfl | hkj
    · simp [hc]
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hfix : wordRep n d (Equiv.swap i j) (Pi.single a (1 : ℂ)) = Pi.single a 1 := by
    rw [wordRep_single]
    congr 1
    funext k
    simp only [Function.comp_apply, Equiv.swap_inv]
    rcases eq_or_ne k i with rfl | hki
    · simp [ha]
    rcases eq_or_ne k j with rfl | hkj
    · simp [ha]
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hm := congrArg (fun f => f (Pi.single a (1 : ℂ))) (h42_columnAlt_mul (d := d) t ⟨_, hτ⟩)
  simp only [Module.End.mul_apply, LinearMap.smul_apply, hfix, signC_def,
    Equiv.Perm.sign_swap hij] at hm
  have : (2 : ℂ) • columnAlt t (Pi.single a (1 : ℂ)) = 0 := by
    rw [two_smul]; nth_rewrite 1 [hm]; simp
  exact (smul_eq_zero.1 this).resolve_left two_ne_zero

theorem h42_colAlt_poly {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    columnAlt t (Pi.single (rowWord t) (1:ℂ)) = polytabloid t := by
  classical
  unfold columnAlt polytabloid
  rw [LinearMap.sum_apply]
  rfl

theorem h42_columnAlt_single {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : Equiv.Perm (Fin n)) :
    columnAlt t (Pi.single (rowWord t ∘ g) 1) ∈
      Submodule.span ℂ {polytabloid t} := by
  classical
  by_cases hcol : ∃ i j, i ≠ j ∧ (t i).val.2 = (t j).val.2 ∧
      (rowWord t ∘ g) i = (rowWord t ∘ g) j
  · obtain ⟨i, j, hij, hc, ha⟩ := hcol
    rw [h42_collision t _ i j hij hc ha]; exact zero_mem _
  push Not at hcol
  let b := rowWord t ∘ g
  let F : Fin n → ℕ × ℕ := fun i => ((b i).val, (t i).val.2)
  have Finj : Function.Injective F := by
    intro i j hF
    by_contra hij
    simp only [F, Prod.mk.injEq] at hF
    exact hcol i j hij hF.2 (Fin.ext hF.1)
  let w : ℕ × ℕ → ℤ := fun p => 2 * ((μ.rowLen p.1 : ℤ) - p.2) - 1
  have hp : ∀ x ∈ μ.cells, 0 < w x := by
    rintro ⟨x1, x2⟩ hx
    have := YoungDiagram.mem_iff_lt_rowLen.1 ((YoungDiagram.mem_cells _).1 hx)
    simp only [w]; omega
  have hn : ∀ x ∉ μ.cells, w x < 0 := by
    rintro ⟨x1, x2⟩ hx
    have : ¬ x2 < μ.rowLen x1 := fun h =>
      hx ((YoungDiagram.mem_cells _).2 (YoungDiagram.mem_iff_lt_rowLen.2 h))
    simp only [w]; omega
  have hsumA : ∑ x ∈ Finset.univ.image F, w x = ∑ i, w (F i) :=
    Finset.sum_image (fun i _ j _ h => Finj h)
  have hsumB : ∑ x ∈ μ.cells, w x = ∑ i, w (t i).val := by
    rw [← Finset.sum_coe_sort μ.cells]
    exact (Equiv.sum_comp t (fun x => w x.val)).symm
  have e1 : ∑ i, (μ.rowLen (rowWord t (g i)).val : ℤ) = ∑ i, (μ.rowLen (rowWord t i).val : ℤ) :=
    Equiv.sum_comp g (fun i => (μ.rowLen (rowWord t i).val : ℤ))
  have hsum : ∑ i, w (F i) = ∑ i, w (t i).val := by
    have a1 : ∀ i, w (F i) = 2 * (μ.rowLen (rowWord t (g i)).val : ℤ) - (2 * ((t i).val.2 : ℤ) + 1) := by
      intro i; simp only [w, F, b, Function.comp_apply]; ring
    have a2 : ∀ i, w (t i).val = 2 * (μ.rowLen (rowWord t i).val : ℤ) - (2 * ((t i).val.2 : ℤ) + 1) := by
      intro i; simp only [w, rowWord]; ring
    simp_rw [a1, a2]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e1]
  have heq := h42_finset_eq (Finset.univ.image F) μ.cells w hp hn (by rw [hsumA, hsumB, hsum])
  have hmem : ∀ i, F i ∈ μ.cells := fun i => heq ▸ Finset.mem_image_of_mem F (Finset.mem_univ i)
  let k : Fin n → Fin n := fun i => t.symm ⟨F i, hmem i⟩
  have kinj : Function.Injective k := by
    intro i j h
    apply Finj
    have := congrArg (fun x => (t x).val) h
    simpa [k] using this
  let h' := Equiv.ofBijective k (Finite.injective_iff_bijective.1 kinj)
  have hmemc : h' ∈ columnGroup t := by
    intro i; simp [h', k, F]
  have hrw : rowWord t ∘ (h' : Equiv.Perm (Fin n)) = b := by
    funext i; apply Fin.ext; simp [h', k, F, rowWord]
  have hb : Pi.single b (1:ℂ) = wordRep n _ h'⁻¹ (Pi.single (rowWord t) 1) := by
    rw [wordRep_single, inv_inv, hrw]
  change columnAlt t (Pi.single b 1) ∈ _
  rw [hb]
  have hm := congrArg (fun f => f (Pi.single (rowWord t) (1:ℂ)))
    (h42_columnAlt_mul (d := μ.colLen 0) t ⟨_, inv_mem hmemc⟩)
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at hm
  rw [hm, h42_colAlt_poly]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem h42_columnAlt_tabloid {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {x : WordSpace n (μ.colLen 0)} (hx : x ∈ tabloidSub t) :
    columnAlt t x ∈ Submodule.span ℂ {polytabloid t} := by
  change x ∈ Submodule.span ℂ _ at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    dsimp only
    rw [wordRep_single]
    exact h42_columnAlt_single t _
  | zero => simp
  | add y z _ _ ihy ihz => rw [map_add]; exact Submodule.add_mem _ ihy ihz
  | smul c y _ ih => rw [map_smul]; exact Submodule.smul_mem _ c ih

theorem h42_poly_rw {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    polytabloid t (rowWord t) = 1 := by
  classical
  unfold polytabloid
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (1 : columnGroup t)]
  · simp
  · intro g _ hg
    have key : rowWord t ∘ (g : Equiv.Perm (Fin n)) ≠ rowWord t := by
      intro h
      apply hg
      ext i : 2
      have h1 := congrFun h i
      have h2 := g.2 i
      have h3 : (t ((g : Equiv.Perm (Fin n)) i)).val = (t i).val := by
        simp only [rowWord, Function.comp_apply, Fin.mk.injEq] at h1
        exact Prod.ext h1 h2
      have := t.injective (Subtype.ext h3)
      simpa using this
    change _ * (Pi.single (rowWord t) (1:ℂ) : WordSpace n _) (rowWord t ∘ (g : Equiv.Perm (Fin n))) = 0
    rw [Pi.single_apply, if_neg key, mul_zero]
  · intro h; exact absurd (@Finset.mem_univ _ (Fintype.ofFinite _) _) h

theorem h42_dot_colAlt {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (u v : WordSpace n d) :
    dotProduct (columnAlt t u) v = dotProduct u (columnAlt t v) := by
  classical
  let _ := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, wordPair_move]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ (fun g => ?_)
  simp [signC_inv]

theorem h42_colAlt_mem {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (P : Subrepresentation (wordRep n d)) (u : WordSpace n d) (hu : u ∈ P.toSubmodule) :
    columnAlt t u ∈ P.toSubmodule := by
  classical
  let _ := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ (fun g _ => Submodule.smul_mem _ _ (P.apply_mem_toSubmodule _ hu))

theorem solution {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Representation.IsIrreducible (spechtRep t) := by
  classical
  have hpS : polytabloid t ∈ (spechtSub t).toSubmodule := mem_cyclic _ _
  have hStab : ∀ x ∈ (spechtSub t).toSubmodule, x ∈ (tabloidSub t).toSubmodule := by
    have hp : polytabloid t ∈ (tabloidSub t).toSubmodule := by
      rw [← h42_colAlt_poly]
      exact h42_colAlt_mem t _ _ (mem_cyclic _ _)
    have := (cyclic_le _ _ (tabloidSub t)).2 hp
    exact fun x hx => this hx
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    have h1 : (⟨polytabloid t, hpS⟩ : Specht t) ∈ (⊤ : Subrepresentation (spechtRep t)).toSubmodule :=
      Submodule.mem_top
    rw [← h] at h1
    have h2 : (⟨polytabloid t, hpS⟩ : Specht t) = 0 := (Submodule.mem_bot ℂ).1 h1
    have h3 := congrArg (fun z : Specht t => z.val (rowWord t)) h2
    simp only [h42_poly_rw] at h3
    exact one_ne_zero h3
  intro W
  by_cases hex : ∃ y ∈ W.toSubmodule, columnAlt t y.val ≠ 0
  · right
    obtain ⟨y, hyW, hy⟩ := hex
    let A := subrepAmbient (spechtSub t) W
    have hyA : y.val ∈ A.toSubmodule := ⟨y, hyW, rfl⟩
    have hcA : columnAlt t y.val ∈ A.toSubmodule := h42_colAlt_mem t A _ hyA
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (h42_columnAlt_tabloid t (hStab _ y.2))
    have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hc; exact hy hc.symm
    have hpA : polytabloid t ∈ A.toSubmodule := by
      have : polytabloid t = c⁻¹ • columnAlt t y.val := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this]; exact Submodule.smul_mem _ _ hcA
    have hle := (cyclic_le _ _ A).2 hpA
    refine eq_top_iff.2 (fun v _ => ?_)
    obtain ⟨w, hw, hwv⟩ := hle v.2
    have : w = v := Subtype.ext hwv
    rw [← this]; exact hw
  · left
    push Not at hex
    refine eq_bot_iff.2 (fun v hv => ?_)
    change v ∈ W.toSubmodule at hv
    show v ∈ (⊥ : Submodule ℂ (Specht t))
    rw [Submodule.mem_bot]
    have hperp : ∀ g, dotProduct v.val (wordRep n (μ.colLen 0) g (polytabloid t)) = 0 := by
      intro g
      have h1 := wordPair_move g⁻¹ v.val (polytabloid t)
      rw [inv_inv] at h1
      rw [← h1, ← h42_colAlt_poly, ← h42_dot_colAlt]
      have h2 := hex _ (W.apply_mem_toSubmodule g⁻¹ hv)
      rw [show wordRep n (μ.colLen 0) g⁻¹ v.val = (spechtRep t g⁻¹ v).val from rfl, h2,
        zero_dotProduct]
    have hall : ∀ x ∈ (spechtSub t).toSubmodule, dotProduct v.val x = 0 := by
      intro x hx
      change x ∈ Submodule.span ℂ _ at hx
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hperp g
      | zero => simp
      | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
      | smul a x _ hx => rw [dotProduct_smul, hx, smul_zero]
    have hs : star v.val ∈ (spechtSub t).toSubmodule := cyclic_star _ (polytabloid_real t) v.2
    have hz := hall _ hs
    let : PartialOrder ℂ := RCLike.toPartialOrder
    let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
    exact Subtype.ext (dotProduct_self_star_eq_zero.mp hz)

