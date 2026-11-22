-- Prove2me | solution 1 for HardyFLocal.clump_fiducial_from_test_table
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T01:16:23.746812+00:00
-- url     : https://prove2.me/submissions/71f4f5b9-5b9a-431f-a637-f32b4a3e0f93

import Mathlib
import Definitions.Def_HardyFLocal_ClumpCausaloid
import Theorems.Thm_HardyFLocal_product_tests_span
import Theorems.Thm_HardyFLocal_clump_coordinate_equivalence
open HardyCausaloid
namespace HardyFLocal
open HardyCausaloid

private theorem fiducial_test_criterion {A R I : Type} [Fintype I] (q : A → R → ℝ)
    (e : I ↪ A) (f : A → I → ℝ) (p : R → I → ℝ) (h : ∀ s i, p s i = q (e i) s)
    (recovers : ∀ a s, q a s = f a ⬝ᵥ p s)
    (spans : Submodule.span ℝ (Set.range p) = ⊤) : Fiducial q (Finset.univ.map e) := by
  classical
  let U := Finset.univ.map e
  let b : I ≃ U := Equiv.ofBijective (fun i => ⟨e i,Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩) ⟨
    fun _ _ hh => e.injective (congrArg Subtype.val hh),by rintro ⟨x,hx⟩; obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx; exact ⟨i,rfl⟩⟩
  have suff : Sufficient q U := by
    intro a
    refine ⟨fun u => f a (b.symm u),fun s => ?_⟩
    rw [recovers, dotProduct, dotProduct, ← b.sum_comp]
    simp [stateVec,h,b]
    rfl
  refine ⟨suff,?_⟩
  have hi : LinearIndependent ℝ (fun i : I => q (e i)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have hz (x : I → ℝ) (hx : x ∈ Submodule.span ℝ (Set.range p)) : c ⬝ᵥ x = 0 := by
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨s,rfl⟩ := hx; simpa [dotProduct,h] using congrFun hc s
      | zero => simp
      | add _ _ _ _ hx hy => simp [dotProduct_add,hx,hy]
      | smul _ _ _ hx => simp [dotProduct_smul,hx]
    simpa using hz (Pi.single i 1) (spans ▸ Submodule.mem_top)
  have indep : LinearIndepOn ℝ q (U : Set A) := by
    change LinearIndependent ℝ (fun j : U => q j.val)
    convert hi.comp b.symm b.symm.injective using 1
    funext j
    exact congrArg q (congrArg Subtype.val (b.apply_symm_apply j)).symm
  intro Z hz hs
  obtain ⟨i,hiU,hiZ⟩ := Finset.exists_of_ssubset hz
  apply (linearIndepOn_iff_notMem_span.mp indep i hiU)
  obtain ⟨c,hc⟩ := hs i
  have hsum : q i = ∑ z : Z, c z • q z.val := by funext s; simpa [dotProduct,stateVec] using hc s
  rw [hsum]
  exact Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨z.val,
    ⟨hz.le z.property,fun eq => hiZ (eq ▸ z.property)⟩,rfl⟩)

end HardyFLocal

open HardyFLocal

open Classical in
theorem solution {m n : ℕ} (M : Model (Setting m n) (Outcome m n))
    (S : FiducialFamily) (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x)
    (hL : IsFiducialLabels S L) (O : Finset (X m n))
    (recovers : ∀ α s, regionTable M O α s = (actualCausaloid S L).r O α ⬝ᵥ (actualCausaloid S L).state M O s)
    {T : Type} [Fintype T] (w : Ω → T → ℝ) (hw : LinearIndependent ℝ w)
    (tests : ∀ t : {i : O × Bool // IsClumpStart O (if i.2 then Sum.inl i.1.val.1 else Sum.inr i.1.val.2) i.1.val} → T,
      ∃ s, ∀ k : omegaC L O, (actualCausaloid S L).state M O s k =
        ∏ i, w (if i.val.2 then (famPairs L O k.val i.val.1.val).1 else (famPairs L O k.val i.val.1.val).2) (t i)) :
    Submodule.span ℝ (Set.range ((actualCausaloid S L).state M O)) = ⊤ ∧
      Fiducial (regionTable M O) ((actualCausaloid S L).fidSet O) := by
  classical
  let C := actualCausaloid S L
  obtain ⟨e,he⟩ := clump_coordinate_equivalence S L hL O
  let I := {i : O × Bool // IsClumpStart O (if i.2 then Sum.inl i.1.val.1 else Sum.inr i.1.val.2) i.1.val}
  let p s (j : I → Ω) := C.state M O s (e.symm j)
  have hspan : Submodule.span ℝ (Set.range p) = ⊤ := by
    apply product_tests_span w hw
    intro t
    obtain ⟨s,hs⟩ := tests t
    refine ⟨s,fun j => ?_⟩
    simpa only [← he, e.apply_symm_apply] using hs (e.symm j)
  let F : ((I → Ω) → ℝ) →ₗ[ℝ] (C.ΩC O → ℝ) := LinearMap.pi fun k => LinearMap.proj (e k)
  have hf : Function.Surjective F := fun f => ⟨fun j => f (e.symm j),funext fun k => congrArg f (e.symm_apply_apply k)⟩
  have thisSpan : Submodule.span ℝ (Set.range (C.state M O)) = ⊤ := by
    have same : C.state M O = F ∘ p := funext fun s => funext fun k => (congrArg (C.state M O s) (e.symm_apply_apply k)).symm
    rw [same,Set.range_comp,← Submodule.map_span,hspan,Submodule.map_top,LinearMap.range_eq_top.mpr hf]
  refine ⟨thisSpan,?_⟩
  let emb : C.ΩC O ↪ Lab (Setting m n) (Outcome m n) O :=
    ⟨fun k => C.embed O k.val, fun _ _ hh => Subtype.ext (C.embed_injective O hh)⟩
  have minimal := fiducial_test_criterion (regionTable M O) emb (C.r O) (C.state M O) (fun _ _ => rfl) recovers thisSpan
  have eqSet : C.fidSet O = Finset.univ.map emb := by
    ext a
    constructor
    · intro ha
      obtain ⟨k,hk,hka⟩ := Finset.mem_map.mp ha
      exact Finset.mem_map.mpr ⟨⟨k,hk⟩,Finset.mem_univ _,hka⟩
    · intro ha
      obtain ⟨k,_,hka⟩ := Finset.mem_map.mp ha
      exact Finset.mem_map.mpr ⟨k.val,k.property,hka⟩
  rw [show (actualCausaloid S L).fidSet O = Finset.univ.map emb from eqSet]
  exact minimal

