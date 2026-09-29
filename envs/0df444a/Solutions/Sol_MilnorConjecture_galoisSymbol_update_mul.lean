-- Prove2me | solution 1 for MilnorConjecture.galoisSymbol_update_mul
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-25T12:05:49.040899+00:00
-- url     : https://prove2.me/submissions/72312ac7-bcd7-4e04-a6ed-481b60e48cae

import Mathlib
import Definitions.Def_MilnorConjecture_MilnorK
import Definitions.Def_MilnorConjecture_GaloisSymbol

open CategoryTheory

namespace MilnorConjecture

section
universe u
variable {k G M : Type u} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [AddCommGroup M] [Module k M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul k M] [IsTopologicalRing k]

lemma curryN_add' {n : ℕ} (F F' : C(Fin n → G, M)) :
    curryN k G M n (F + F') = curryN k G M n F + curryN k G M n F' := by
  have := curryN_sub (k := k) (F + F') F'
  rw [add_sub_cancel_right] at this
  rw [this, sub_add_cancel]

lemma liftCycles_add_gen {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex (TopModuleCat k) c)
    {A : TopModuleCat k} {i : ι} (f g : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hf : f ≫ K.d i j = 0) (hg : g ≫ K.d i j = 0) (hfg : (f + g) ≫ K.d i j = 0) :
    K.liftCycles (f + g) j hj hfg = K.liftCycles f j hj hf + K.liftCycles g j hj hg := by
  rw [← cancel_mono (K.iCycles i)]
  simp [Preadditive.add_comp]

/-- class of a cycle given as an element. -/
noncomputable def clsAux (n : ℕ) (σ : (trivialRep k G M).homogeneousCochains.X n)
    (hσ : TopModuleCat.ofHom (ContinuousLinearMap.toSpanSingleton k σ) ≫
      (trivialRep k G M).homogeneousCochains.d n (n + 1) = 0) :
    continuousCohomology n (trivialRep k G M) :=
  (ContinuousCohomology.π _ n).hom
    (((trivialRep k G M).homogeneousCochains.liftCycles
      (TopModuleCat.ofHom (ContinuousLinearMap.toSpanSingleton k σ)) (n + 1) (by simp) hσ).hom 1)

lemma hσ_of_d (n : ℕ) (σ : (trivialRep k G M).homogeneousCochains.X n)
    (hd : ((trivialRep k G M).homogeneousCochains.d n (n + 1)).hom σ = 0) :
    TopModuleCat.ofHom (ContinuousLinearMap.toSpanSingleton k σ) ≫
      (trivialRep k G M).homogeneousCochains.d n (n + 1) = 0 := by
  let ι : TopModuleCat.of k k ⟶ (trivialRep k G M).homogeneousCochains.X n :=
    TopModuleCat.ofHom (ContinuousLinearMap.toSpanSingleton k σ)
  show ι ≫ _ = 0
  apply ConcreteCategory.ext
  apply ContinuousLinearMap.ext_ring
  have h1 : ι 1 = σ := one_smul k σ
  rw [ConcreteCategory.comp_apply, h1]
  simpa using hd

lemma d_curry_zero (n : ℕ) (H : C(Fin (n + 1) → G, M))
    (hi : ∀ (g : G) (v : Fin (n + 1) → G), H (fun i ↦ g * v i) = H v)
    (hc : coboundary (n + 1) H = 0) :
    ((trivialRep k G M).homogeneousCochains.d n (n + 1)).hom
      (⟨curryN k G M (n + 1) H, curryN_mem_invariants H hi⟩ :
        (trivialRep k G M).homogeneousCochains.X n) = 0 := by
  apply Subtype.ext
  erw [TopRep.homogeneousCochains.d_apply]
  change ((trivialRep k G M).d (n + 1)).hom (curryN k G M (n + 1) H) = 0
  rw [d_curryN, hc, curryN_zero]

lemma clsAux_congr (n : ℕ) (σ τ : (trivialRep k G M).homogeneousCochains.X n) (h : σ = τ) hσ hτ :
    clsAux (k := k) (G := G) (M := M) n σ hσ = clsAux n τ hτ := by
  subst h; rfl

lemma clsAux_add (n : ℕ) (σ τ : (trivialRep k G M).homogeneousCochains.X n) hσ hτ hστ :
    clsAux (k := k) (G := G) (M := M) n (σ + τ) hστ = clsAux n σ hσ + clsAux n τ hτ := by
  unfold clsAux
  rw [← map_add, ← add_apply, ← TopModuleCat.hom_add]
  congr 3
  rw [← cancel_mono (HomologicalComplex.iCycles _ _)]
  simp only [Preadditive.add_comp]
  erw [HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i,
    HomologicalComplex.liftCycles_i]
  apply ConcreteCategory.ext
  apply ContinuousLinearMap.ext_ring
  exact smul_add (1 : k) σ τ

lemma classOf_add' (n : ℕ) (F F' : C(Fin (n + 1) → G, M))
    (hinv : ∀ (g : G) (v : Fin (n + 1) → G), F (fun i ↦ g * v i) = F v)
    (hcoc : coboundary (n + 1) F = 0)
    (hinv' : ∀ (g : G) (v : Fin (n + 1) → G), F' (fun i ↦ g * v i) = F' v)
    (hcoc' : coboundary (n + 1) F' = 0)
    (hinv'' : ∀ (g : G) (v : Fin (n + 1) → G), (F + F') (fun i ↦ g * v i) = (F + F') v)
    (hcoc'' : coboundary (n + 1) (F + F') = 0) :
    classOf k n (F + F') hinv'' hcoc'' = classOf k n F hinv hcoc + classOf k n F' hinv' hcoc' := by
  have e : ∀ (H : C(Fin (n + 1) → G, M)) hi hc, classOf k n H hi hc =
      clsAux n ⟨curryN k G M (n + 1) H, curryN_mem_invariants H hi⟩
        (hσ_of_d n _ (d_curry_zero n H hi hc)) := fun _ _ _ ↦ rfl
  rw [e, e, e]
  let σ₁ : (trivialRep k G M).homogeneousCochains.X n :=
    ⟨curryN k G M (n + 1) F, curryN_mem_invariants F hinv⟩
  let σ₂ : (trivialRep k G M).homogeneousCochains.X n :=
    ⟨curryN k G M (n + 1) F', curryN_mem_invariants F' hinv'⟩
  have hd : ((trivialRep k G M).homogeneousCochains.d n (n + 1)).hom (σ₁ + σ₂) = 0 := by
    rw [map_add]
    rw [d_curry_zero n F hinv hcoc, d_curry_zero n F' hinv' hcoc', add_zero]
  calc _ = clsAux n (σ₁ + σ₂) (hσ_of_d n _ hd) :=
        clsAux_congr _ _ _ (Subtype.ext (curryN_add' F F')) _ _
    _ = _ := clsAux_add _ _ _ _ _ _

lemma classOf_congr' (n : ℕ) (F F' : C(Fin (n + 1) → G, M)) (h : F = F') hinv hcoc hinv' hcoc' :
    classOf k n F hinv hcoc = classOf k n F' hinv' hcoc' := by
  subst h; rfl
end

variable {F : Type} [Field F] [NeZero (2 : F)]

lemma kummerCharFun_units_mul (x y : Fˣ) (σ : AbsGal F) :
    kummerCharFun (x * y) σ = kummerCharFun x σ + kummerCharFun y σ := by
  have hxy : sqrtSep (x * y) = sqrtSep x * sqrtSep y ∨ sqrtSep (x * y) = -(sqrtSep x * sqrtSep y) := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [sqrtSep_sq, mul_pow, sqrtSep_sq, sqrtSep_sq, Units.val_mul, map_mul]
  have hne : -(sqrtSep x * sqrtSep y) ≠ sqrtSep x * sqrtSep y := by
    intro h
    have h2 : (2 : SeparableClosure F) * (sqrtSep x * sqrtSep y) = 0 := by
      rw [two_mul]; nth_rw 1 [← h]; ring
    rcases mul_eq_zero.mp h2 with h2 | h2
    · exact NeZero.ne ((2 : ℕ) : SeparableClosure F) (by exact_mod_cast h2)
    · exact mul_ne_zero (sqrtSep_ne_zero x) (sqrtSep_ne_zero y) h2
  have hnx := neg_sqrtSep_ne x
  have hny := neg_sqrtSep_ne y
  have key : σ (sqrtSep (x * y)) = sqrtSep (x * y) ↔
      σ (sqrtSep x * sqrtSep y) = sqrtSep x * sqrtSep y := by
    rcases hxy with h | h
    · rw [h]
    · rw [h, map_neg, neg_inj]
  unfold kummerCharFun
  rw [map_mul] at key
  rcases apply_sqrtSep x σ with hx | hx <;> rcases apply_sqrtSep y σ with hy | hy <;>
    rw [hx, hy] at key <;>
    by_cases h : σ (sqrtSep (x * y)) = sqrtSep (x * y) <;>
    simp only [h, hx, hy, if_true, if_false, hnx, hny] <;> simp_all <;> decide

lemma symbolCochain_update_mul {n : ℕ} (a : Fin n → Fˣ) (i : Fin n) (x y : Fˣ) :
    symbolCochain (Function.update a i (x * y)) =
      symbolCochain (Function.update a i x) + symbolCochain (Function.update a i y) := by
  ext v
  simp only [symbolCochain, ContinuousMap.coe_mk, ContinuousMap.add_apply, prodCochain, kummerChar]
  rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i,
    Fintype.prod_eq_mul_prod_compl i]
  have hrest : ∀ z : Fˣ, ∏ j ∈ ({i} : Finset (Fin n))ᶜ,
      (kummerCharFun (Function.update a i z j) (v j.succ) -
        kummerCharFun (Function.update a i z j) (v j.castSucc)) =
      ∏ j ∈ ({i} : Finset (Fin n))ᶜ,
      (kummerCharFun (a j) (v j.succ) - kummerCharFun (a j) (v j.castSucc)) := by
    intro z
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    have hji : j ≠ i := by simpa using hj
    rw [Function.update_of_ne hji]
  simp only [hrest, Function.update_self, kummerCharFun_units_mul]
  ring

end MilnorConjecture

open MilnorConjecture in
theorem solution (F : Type) [Field F] [NeZero (2 : F)] (n : ℕ)
    (a : Fin n → Fˣ) (i : Fin n) (x y : Fˣ) :
    galoisSymbol (Function.update a i (x * y)) =
      galoisSymbol (Function.update a i x) + galoisSymbol (Function.update a i y) := by
  unfold galoisSymbol
  rw [← classOf_add']
  · exact classOf_congr' _ _ _ (symbolCochain_update_mul a i x y) _ _ _ _
  · intro g v
    rw [← symbolCochain_update_mul]
    exact symbolCochain_invariant _ g v
  · rw [← symbolCochain_update_mul]
    exact coboundary_symbolCochain _
