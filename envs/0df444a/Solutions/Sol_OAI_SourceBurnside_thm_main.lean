-- Prove2me | solution 1 for OAI.SourceBurnside.thm_main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T16:13:41.35563+00:00
-- url     : https://prove2.me/submissions/813309c9-da7b-49b7-895c-9a16303f74bb

import Mathlib
import Definitions.Def_PeriodicGroup
import Definitions.Def_OAIQ18Pg011
import Definitions.Def_OAIQ18Pg014
import Theorems.Thm_OAI_SourceBurnside_ConcreteSource_matrix_nil_kernel
import Theorems.Thm_OAI_SourceBurnside_ConcreteSource_matrix_periodic
import Theorems.Thm_OAI_SourceBurnside_ConcreteSource_steinberg_infinite

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_MonomialPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside

namespace FiniteSteinbergPresentation

open MonomialCompletion

variable {n : ℕ} {α : Type u}

 theorem rel_finite [Finite α] : {r | Rel n α r}.Finite := by
  let S₁ := Set.range (fun g : Gen n α => FreeGroup.of g ^ 2)
  let S₂ := Set.range (fun g : Gen n α × Gen n α => bracket (FreeGroup.of g.1) (FreeGroup.of g.2))
  let S₃ := Set.range (fun g : Gen n α × Gen n α × Gen n α =>
    bracket (FreeGroup.of g.1) (FreeGroup.of g.2.1) * (FreeGroup.of g.2.2)⁻¹)
  apply ((Set.finite_range _).union ((Set.finite_range _).union (Set.finite_range _)) :
    (S₁ ∪ (S₂ ∪ S₃)).Finite).subset
  intro r hr
  cases hr with
  | square p w => exact Or.inl ⟨(p, w), rfl⟩
  | commute p q h₁ h₂ u v => exact Or.inr (Or.inl ⟨((p, u), (q, v)), rfl⟩)
  | product i j k hij hjk hik u v h =>
    exact Or.inr (Or.inr ⟨((⟨i, j, hij⟩, u), (⟨j, k, hjk⟩, v),
      (⟨i, k, hik⟩, ⟨u.val ++ v.val, by simpa only [List.length_append] using h⟩)), rfl⟩)

end FiniteSteinbergPresentation
end SourceBurnside
end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_KernelRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside

namespace Steinberg
variable {n m : ℕ} {R : Type u} [Ring R]

lemma outside (hn : 3 ≤ n) (p : Root n) : ∃ k : Fin n, k ≠ p.row ∧ k ≠ p.col := by
  have hc : ({p.row,p.col} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    have h := (Finset.card_le_two : ({p.row,p.col} : Finset (Fin n)).card ≤ 2)
    simpa using (lt_of_le_of_lt h (show 2 < n by omega))
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  exact ⟨k, by simpa using hk⟩

theorem hom_to_commGroup_trivial (hn : 3 ≤ n) {A : Type v} [CommGroup A]
    (f : Steinberg n R →* A) : f = 1 := by
  apply hom_ext
  intro p a
  obtain ⟨k,hki,hkj⟩ := outside hn p
  have hb := x_mul p.row k p.col hki.symm hkj p.ne a (1 : R)
  rw [mul_one] at hb
  rw [← hb, map_bracket]
  simp [bracket, mul_comm]

end Steinberg
end SourceBurnside

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R]
lemma kernel_commutes_column (t : Fin n) {g : Steinberg n R} (hg : g∈away t)
    (hmat : Elementary.representation g=1) (i : Fin n) (hi : i≠t) (a : R) :
    Commute g (Steinberg.x ⟨i,t,hi⟩ a) := by
  let x := Steinberg.x ⟨i,t,hi⟩ a
  have hx : x∈columnStrip t := column_root_mem t i hi a
  have hc : g*x*g⁻¹∈columnStrip t := (Subgroup.mem_normalizer_iff.mp (away_le_column_normalizer t hg) x).mp hx
  have H := strip_faithful (awayCoordinates t) {t} (away_disjoint t)
    ((columnStrip t).mul_mem hc ((columnStrip t).inv_mem hx)) (by simp [map_mul,map_inv,hmat])
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp H)
lemma kernel_commutes_row (t : Fin n) {g : Steinberg n R} (hg : g∈away t)
    (hmat : Elementary.representation g=1) (i : Fin n) (hi : t≠i) (a : R) :
    Commute g (Steinberg.x ⟨t,i,hi⟩ a) := by
  let x := Steinberg.x ⟨t,i,hi⟩ a
  have hx : x∈rowStrip t := row_root_mem t i hi a
  have hc : g*x*g⁻¹∈rowStrip t := (Subgroup.mem_normalizer_iff.mp (away_le_row_normalizer t hg) x).mp hx
  have H := strip_faithful {t} (awayCoordinates t) (away_disjoint t).symm
    ((rowStrip t).mul_mem hc ((rowStrip t).inv_mem hx)) (by simp [map_mul,map_inv,hmat])
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp H)

theorem supported_kernel_central (t : Fin n) {g : Steinberg n R} (hg : g∈away t)
    (hmat : Elementary.representation g=1) : g∈Subgroup.center (Steinberg n R) := by
  have hc (p : Root n) (a : R) : Commute g (Steinberg.x p a) := by
    by_cases hr : p.row=t
    · have hp : p=⟨t,p.col,hr ▸ p.ne⟩ := by cases p;cases hr;rfl
      rw [hp]
      exact kernel_commutes_row t hg hmat p.col (hr ▸ p.ne) a
    · by_cases ht : p.col=t
      · have hp : p=⟨p.row,t,ht ▸ p.ne⟩ := by cases p;cases ht;rfl
        rw [hp]
        exact kernel_commutes_column t hg hmat p.row (ht ▸ p.ne) a
      · have he := Steinberg.x_mul p.row t p.col hr (Ne.symm ht) p.ne a (1:R)
        rw [mul_one] at he
        have HH := CommutatorCalculus.commute_bracket_right
          (kernel_commutes_column t hg hmat p.row hr a)
          (kernel_commutes_row t hg hmat p.col (Ne.symm ht) 1)
        exact he ▸ HH
  have hf : (MulAut.conj g).toMonoidHom=MonoidHom.id (Steinberg n R) := by
    apply Steinberg.hom_ext
    intro p a
    change g*Steinberg.x p a*g⁻¹=Steinberg.x p a
    rw [(hc p a).eq,mul_inv_cancel_right]
  apply Subgroup.mem_center_iff.mpr
  intro x
  have H := DFunLike.congr_fun hf x
  change g*x*g⁻¹=x at H
  exact (mul_inv_eq_iff_eq_mul.mp H).symm
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R]
lemma coordinateIndex_ne_spare (i : Fin n) : coordinateIndex n i≠spareCoordinate n := by
  intro he
  have := (coordinateEquiv n).injective he
  contradiction

lemma padUnitsHom_e (p : Root n) (a : R) :
    padUnitsHom (Elementary.e p a)=Elementary.e (p.map (coordinateIndex n) (coordinateIndex_injective n)) a := by
  apply Units.ext
  change (Matrix.fromBlocks (1+Matrix.single p.row p.col a) 0 0 1).submatrix
    (coordinateEquiv n).symm (coordinateEquiv n).symm =
      1+Matrix.single (coordinateIndex n p.row) (coordinateIndex n p.col) a
  apply Matrix.ext
  intro i j
  obtain ⟨i,rfl⟩ := (coordinateEquiv n).surjective i
  obtain ⟨j,rfl⟩ := (coordinateEquiv n).surjective j
  cases i <;> cases j <;>
    simp [coordinateIndex,Matrix.submatrix_apply,Matrix.fromBlocks,Matrix.add_apply,Matrix.one_apply,Matrix.single_apply]

lemma pad_representation :
    Elementary.representation.comp (padSteinberg (n:=n) (R:=R))=
      padUnitsHom.comp Elementary.representation := by
  apply Steinberg.hom_ext
  intro p a
  simp only [MonoidHom.comp_apply,padSteinberg,Steinberg.coordinateMap_x,Elementary.representation_x,padUnitsHom_e]
lemma pad_mem_away (g : Steinberg n R) : padSteinberg g∈away (spareCoordinate n) := by
  have H : (⊤ : Subgroup (Steinberg n R)) ≤ (away (spareCoordinate n)).comap padSteinberg := by
    rw [←Steinberg.closure_range_x]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨⟨p,a⟩,rfl⟩
    apply Subgroup.subset_closure
    exact ⟨p.map (coordinateIndex n) (coordinateIndex_injective n),a,
      coordinateIndex_ne_spare p.row,coordinateIndex_ne_spare p.col,by simp [padSteinberg]⟩
  exact H (Subgroup.mem_top g)

theorem stabilized_kernel_central (g : Steinberg n R) (hg : Elementary.representation g=1) :
    padSteinberg g∈Subgroup.center (Steinberg (n+1) R) := by
  apply supported_kernel_central (spareCoordinate n) (pad_mem_away g)
  have he := DFunLike.congr_fun (pad_representation (n:=n) (R:=R)) g
  simpa only [MonoidHom.comp_apply,hg,map_one] using he
end
end SourceBurnside.Kernel

namespace SourceBurnside.Steinberg
noncomputable section
variable {n : ℕ} {R G H : Type*} [Ring R] [Group G] [Group H]

lemma finite_central_image_periodic (hn : 3≤n) [Finite H]
    (f : Steinberg n R →* G) (ρ : G →* H)
    (hc : ∀g : Steinberg n R,ρ (f g)=1 → f g∈Subgroup.center G) :
    ∀g : Steinberg n R,∃ m : ℕ, 0 < m ∧ (f g)^m=1 := by
  let F := f.range
  let ψ : F →* H := ρ.comp F.subtype
  have hcen : ψ.ker ≤ Subgroup.center F := by
    rintro x hx
    obtain ⟨g,hg⟩ := x.property
    have hx' : ρ (f g)=1 := by
      change ρ x.val=1 at hx
      exact hg ▸ hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    change y.val * x.val = x.val * y.val
    rw [← hg]
    exact Subgroup.mem_center_iff.mp (hc g hx') y.val
  let : ψ.ker.FiniteIndex := Subgroup.finiteIndex_ker ψ
  let : (Subgroup.center F).FiniteIndex := Subgroup.finiteIndex_of_le hcen
  let : CommGroup (Subgroup.center F) :=
    { (inferInstance : Group (Subgroup.center F)) with
      mul_comm := fun a b=>Subtype.ext (b.property.comm a).symm }
  let θ : Steinberg n R →* Subgroup.center F := (MonoidHom.transferCenterPow F).comp f.rangeRestrict
  have hθ : θ=1 := hom_to_commGroup_trivial hn θ
  intro g
  refine ⟨(Subgroup.center F).index,Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero,?_⟩
  have he := congrArg (fun z : Subgroup.center F=>z.val.val) (DFunLike.congr_fun hθ g)
  simp only [θ,MonoidHom.comp_apply,MonoidHom.transferCenterPow_apply,MonoidHom.one_apply,
    OneMemClass.coe_one,Subgroup.coe_pow] at he
  change (f g) ^ (Subgroup.center F).index = 1 at he
  exact he
end
end SourceBurnside.Steinberg
namespace SourceBurnside.Kernel
noncomputable section
variable {n : ℕ} {R : Type*} [Ring R]
lemma padUnitsHom_injective : Function.Injective (padUnitsHom (n:=n) (R:=R)) := by
  intro u v huv
  apply Units.ext
  have he := congrArg Units.val huv
  change (Matrix.reindexRingEquiv R (coordinateEquiv n)) (Matrix.fromBlocks u.val 0 0 1)=
    (Matrix.reindexRingEquiv R (coordinateEquiv n)) (Matrix.fromBlocks v.val 0 0 1) at he
  have hb := (Matrix.reindexRingEquiv R (coordinateEquiv n)).injective he
  apply Matrix.ext
  intro i j
  exact congrArg (fun M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R=>M (Sum.inl i) (Sum.inl j)) hb
lemma pad_kernel_iff (g : Steinberg n R) :
    Elementary.representation (padSteinberg g)=1 ↔ Elementary.representation g=1 := by
  have he := DFunLike.congr_fun (pad_representation (n:=n) (R:=R)) g
  change Elementary.representation (padSteinberg g)=padUnitsHom (Elementary.representation g) at he
  rw [he]
  exact (map_eq_one_iff _ padUnitsHom_injective)

theorem stabilized_field_periodic (hn : 3≤n) (g : Steinberg n (ZMod 2)) :
    ∃ m : ℕ, 0 < m ∧ (padSteinberg g)^m=1 := by
  apply Steinberg.finite_central_image_periodic hn padSteinberg Elementary.representation
  intro u hu
  exact stabilized_kernel_central u ((pad_kernel_iff u).mp hu)
end
end SourceBurnside.Kernel

namespace SourceBurnside.Elementary
variable {n : ℕ} {R S : Type*} [Ring R] [Ring S]
lemma map_kernel (f : R →+* S) (g : Steinberg n R) (hg : representation g=1) :
    representation (Steinberg.map f g)=1 := by
  have he := DFunLike.congr_fun (representation_map (n:=n) f) g
  simpa only [MonoidHom.comp_apply,hg,map_one] using he
end SourceBurnside.Elementary
namespace SourceBurnside.Steinberg
variable {n : ℕ} {R S T : Type*} [Ring R] [Ring S] [Ring T]
lemma map_comp (g : S →+* T) (f : R →+* S) :
    (map (n:=n) g).comp (map f)=map (g.comp f) := by
  apply hom_ext
  intro p a
  simp [map_x]
lemma map_map (g : S →+* T) (f : R →+* S) (x : Steinberg n R) :
    map g (map f x)=map (g.comp f) x := DFunLike.congr_fun (map_comp g f) x
lemma map_identity : map (n:=n) (RingHom.id R)=MonoidHom.id _ := by
  apply hom_ext
  intro p a
  simp [map_x]
@[simp] lemma map_identity_apply (x : Steinberg n R) : map (RingHom.id R) x=x :=
  DFunLike.congr_fun map_identity x
end SourceBurnside.Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_BlockEmbeddings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
lemma flatten_single (i j : Fin n) (s t : Fin N) (a : R) :
    flattenRing (Matrix.single i j (Matrix.single s t a))=Matrix.single (blockIndex i s) (blockIndex j t) a := by
  ext u v
  obtain ⟨⟨i',s'⟩,rfl⟩ := finProdFinEquiv.surjective u
  obtain ⟨⟨j',t'⟩,rfl⟩ := finProdFinEquiv.surjective v
  simp only [flattenRing,RingEquiv.trans_apply,Matrix.coe_reindexRingEquiv,Matrix.reindex_apply,
    Matrix.submatrix_apply,Equiv.symm_apply_apply,Matrix.compRingEquiv_apply,Matrix.comp_apply]
  by_cases hi : i=i' <;> by_cases hj : j=j' <;> by_cases hs : s=s' <;> by_cases ht : t=t' <;>
    simp_all [Matrix.single,blockIndex,Prod.ext_iff]

lemma representation_blockRoot (p : Root n) (A : Matrix (Fin N) (Fin N) R) :
    Elementary.representation (blockRoot p A)=Units.map flattenRing.toMonoidHom (Elementary.e p A) := by
  induction A using Matrix.induction_on' with
  | h_zero => simp [blockRoot_zero]
  | h_add A B hA hB => rw [blockRoot_add,map_mul,hA,hB,Elementary.e_add,map_mul]
  | h_std_basis s t a =>
    rw [blockRoot_single,Elementary.representation_x]
    apply Units.ext
    change 1+Matrix.single (blockIndex p.row s) (blockIndex p.col t) a=
      flattenRing (1+Matrix.single p.row p.col (Matrix.single s t a))
    rw [map_add,map_one,flatten_single]
lemma block_representation :
    Elementary.representation.comp (blockMap (n:=n) (N:=N) (R:=R))=
      (Units.map flattenRing.toMonoidHom).comp Elementary.representation := by
  apply Steinberg.hom_ext
  intro p A
  simp only [MonoidHom.comp_apply,blockMap_x,Elementary.representation_x,representation_blockRoot]
lemma blockMap_kernel (g : Steinberg n (Matrix (Fin N) (Fin N) R))
    (hg : Elementary.representation g=1) : Elementary.representation (blockMap g)=1 := by
  have he := DFunLike.congr_fun (block_representation (n:=n) (N:=N) (R:=R)) g
  simpa only [MonoidHom.comp_apply,hg,map_one] using he
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R]

lemma root_rowFixed (i : Fin n) (p : Root n) (h : p.row≠i) (a : R) :
    Elementary.representation (Steinberg.x p a)∈rowFixed i := by
  intro j
  simp [Elementary.representation_x,Elementary.coe_e,Matrix.single,h]
lemma strip_eq_one_of_rows (H L : Finset (Fin n)) (hd : Disjoint H L)
    {g : Steinberg n R} (hg : g∈Strip H L hd)
    (hrows : ∀i∈H,Elementary.representation g∈rowFixed i) : g=1 := by
  obtain ⟨A,rfl⟩ := strip_le_range H L hd hg
  have hA : A=1 := by
    funext p
    have he := hrows p.1.val p.1.property p.2.val
    rw [←MonoidHom.comp_apply,representation_rectRoot] at he
    change (1+rectMatrix H L A) p.1.val p.2.val=(1 : Matrix (Fin n) (Fin n) R) p.1.val p.2.val at he
    rw [Matrix.add_apply,rectMatrix_entry] at he
    apply Multiplicative.toAdd.injective
    exact add_left_cancel (he.trans (add_zero _).symm)
  rw [hA,map_one]

lemma right_conjugate_strip_root (H L : Finset (Fin n)) (hd : Disjoint H L)
    (p : Root n) (hr : p.row∈L) (hc : p.col∈L) (a : R)
    (q : RectIndex H L) (b : R) :
    Steinberg.x p a*Steinberg.x (rectPosition H L hd q) b*(Steinberg.x p a)⁻¹∈Strip H L hd := by
  have hcol : p.col≠q.1.val := fun he=>Finset.disjoint_left.mp hd q.1.property (he ▸ hc)
  by_cases he : p.row=q.2.val
  · have hp : p=⟨q.2.val,p.col,he ▸ p.ne⟩ := by cases p;cases he;rfl
    rw [hp]
    dsimp only [rectPosition]
    rw [Steinberg.conjugate_reverse q.1.val q.2.val p.col (rectPosition H L hd q).ne (he ▸ p.ne) hcol.symm b a]
    apply (Strip H L hd).mul_mem
    · exact Subgroup.subset_closure ⟨(q.1,⟨p.col,hc⟩),-(b*a),rfl⟩
    · exact Subgroup.subset_closure ⟨q,b,rfl⟩
  · rw [Steinberg.conjugate_commute p (rectPosition H L hd q) hcol he]
    exact Subgroup.subset_closure ⟨q,b,rfl⟩
lemma right_conjugate_strip (H L : Finset (Fin n)) (hd : Disjoint H L)
    (p : Root n) (hr : p.row∈L) (hc : p.col∈L) (a : R)
    {g : Steinberg n R} (hg : g∈Strip H L hd) :
    Steinberg.x p a*g*(Steinberg.x p a)⁻¹∈Strip H L hd := by
  have Hle : Strip H L hd ≤ (Strip H L hd).comap (MulAut.conj (Steinberg.x p a)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨q,b,rfl⟩
    exact right_conjugate_strip_root H L hd p hr hc a q b
  exact Hle hg

lemma deeper_normalizes_strip (height : Fin n→ℕ) (k : ℕ) :
    triangular (R:=R) height (k+1)≤Subgroup.normalizer
      (Strip (layer height k) (above height k) (layer_above_disjoint height k) (R:=R) : Set (Steinberg n R)) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨p,a,hk,hp,rfl⟩
  have hr : p.row∈above height k := by simp [above];omega
  have hc : p.col∈above height k := by simp [above];omega
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · exact right_conjugate_strip _ _ _ p hr hc a
  · intro hx
    have hx' := right_conjugate_strip _ _ (layer_above_disjoint height k) p hr hc (-a) hx
    simpa only [Steinberg.x_neg,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hx'
lemma deeper_fixes_layer (height : Fin n→ℕ) (k : ℕ) (i : Fin n) (hi : i∈layer height k) :
    triangular (R:=R) height (k+1)≤(rowFixed i).comap Elementary.representation := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨p,a,hk,hp,rfl⟩
  apply root_rowFixed
  intro he
  simp only [layer,Finset.mem_filter,Finset.mem_univ,true_and] at hi
  rw [he,hi] at hk
  omega
lemma triangular_split (height : Fin n→ℕ) (k : ℕ) {g : Steinberg n R}
    (hg : g∈triangular height k) :
    ∃a∈Strip (layer height k) (above height k) (layer_above_disjoint height k),
      ∃b∈triangular height (k+1),g=a*b := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨p,a,hk,hp,rfl⟩ := hg
    by_cases he : height p.row=k
    · refine ⟨Steinberg.x p a,?_,1,Subgroup.one_mem _,(mul_one _).symm⟩
      apply Subgroup.subset_closure
      have hr : p.row∈layer height k := by simp [layer,he]
      have hc : p.col∈above height k := by simp [above];omega
      exact ⟨(⟨p.row,hr⟩,⟨p.col,hc⟩),a,by congr⟩
    · refine ⟨1,Subgroup.one_mem _,Steinberg.x p a,?_,(one_mul _).symm⟩
      exact Subgroup.subset_closure ⟨p,a,by omega,hp,rfl⟩
  | one => exact ⟨1,Subgroup.one_mem _,1,Subgroup.one_mem _,(one_mul _).symm⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨a,ha,b,hb,rfl⟩ := ihx
    obtain ⟨c,hc,d,hd,rfl⟩ := ihy
    have hbc : b*c*b⁻¹∈Strip (layer height k) (above height k) (layer_above_disjoint height k) :=
      (Subgroup.mem_normalizer_iff.mp (deeper_normalizes_strip height k hb) c).mp hc
    exact ⟨a*(b*c*b⁻¹),Subgroup.mul_mem _ ha hbc,b*d,Subgroup.mul_mem _ hb hd,by simp [mul_assoc]⟩
  | inv x hx ih =>
    obtain ⟨a,ha,b,hb,rfl⟩ := ih
    have hbi := (triangular (R:=R) height (k+1)).inv_mem hb
    have hai := (Strip (layer height k) (above height k) (layer_above_disjoint height k)).inv_mem ha
    have hconj : b⁻¹*a⁻¹*b∈Strip (layer height k) (above height k) (layer_above_disjoint height k) := by
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp (deeper_normalizes_strip height k hbi) a⁻¹).mp hai
    exact ⟨b⁻¹*a⁻¹*b,hconj,b⁻¹,hbi,by simp [mul_assoc]⟩
lemma triangular_faithful_aux (height : Fin n→ℕ) (d k : ℕ)
    (hbound : ∀i,height i<k+d) {g : Steinberg n R}
    (hg : g∈triangular height k) (hmat : Elementary.representation g=1) : g=1 := by
  induction d generalizing k g with
  | zero =>
    have hbot : triangular (R:=R) height k≤⊥ := by
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨p,a,hk,hp,rfl⟩
      have hb := hbound p.row
      omega
    exact (Subgroup.mem_bot.mp (hbot hg))
  | succ d ih =>
    obtain ⟨a,ha,b,hb,rfl⟩ := triangular_split height k hg
    have he : a=1 := by
      apply strip_eq_one_of_rows _ _ (layer_above_disjoint height k) ha
      intro i hi
      have hbi := deeper_fixes_layer (R:=R) height k i hi ((triangular height (k+1)).inv_mem hb)
      have hab : Elementary.representation a=Elementary.representation b⁻¹ := by
        rw [map_inv]
        exact eq_inv_of_mul_eq_one_left (by simpa only [map_mul] using hmat)
      rw [hab]
      exact hbi
    rw [he,one_mul] at hmat ⊢
    apply ih (k+1) _ hb hmat
    intro i
    have h := hbound i
    omega

theorem triangular_faithful (height : Fin n→ℕ) (B : ℕ) (hbound : ∀i,height i<B)
    {g : Steinberg n R} (hg : g∈triangular height 0)
    (hmat : Elementary.representation g=1) : g=1 :=
  triangular_faithful_aux height B 0 (by simpa only [zero_add] using hbound) hg hmat
lemma level_conjugate_triangular_root (height : Fin n→ℕ) (k : ℕ)
    (p : Root n) (hp : height p.row=height p.col) (a : R)
    (q : Root n) (hqk : k≤height q.row) (hq : height q.row<height q.col) (b : R) :
    Steinberg.x p a*Steinberg.x q b*(Steinberg.x p a)⁻¹∈triangular height k := by
  by_cases hc : p.col=q.row
  · have hjk : p.col≠q.col := hc ▸ q.ne
    have hik : p.row≠q.col := by
      intro he
      have heh := congrArg height he
      rw [hc] at hp
      omega
    have hqeq : q=⟨p.col,q.col,hjk⟩ := by cases q;cases hc;rfl
    rw [hqeq,Steinberg.conjugate_chain p.row p.col q.col p.ne hjk hik a b]
    apply Subgroup.mul_mem
    · apply Subgroup.subset_closure
      exact ⟨⟨p.row,q.col,hik⟩,a*b,by rw [hp,hc];exact hqk,by rw [hp,hc];exact hq,rfl⟩
    · exact Subgroup.subset_closure ⟨⟨p.col,q.col,hjk⟩,b,by simpa only [hc] using hqk,by simpa only [hc] using hq,rfl⟩
  · by_cases hr : p.row=q.col
    · have hij : q.row≠p.row := hr ▸ q.ne
      have hik : q.row≠p.col := by
        intro he
        have heh := congrArg height he
        rw [hr] at hp
        omega
      have hqeq : q=⟨q.row,p.row,hij⟩ := by cases q;cases hr;rfl
      rw [hqeq,Steinberg.conjugate_reverse q.row p.row p.col hij p.ne hik b a]
      apply Subgroup.mul_mem
      · apply Subgroup.subset_closure
        refine ⟨⟨q.row,p.col,hik⟩,-(b*a),hqk,?_,rfl⟩
        rw [←hp,hr]
        exact hq
      · exact Subgroup.subset_closure ⟨⟨q.row,p.row,hij⟩,b,hqk,by simpa only [hr] using hq,rfl⟩
    · rw [Steinberg.conjugate_commute p q hc hr]
      exact Subgroup.subset_closure ⟨q,b,hqk,hq,rfl⟩
lemma level_conjugate_triangular (height : Fin n→ℕ) (k : ℕ)
    (p : Root n) (hp : height p.row=height p.col) (a : R)
    {g : Steinberg n R} (hg : g∈triangular height k) :
    Steinberg.x p a*g*(Steinberg.x p a)⁻¹∈triangular height k := by
  have H : triangular (R:=R) height k≤(triangular height k).comap (MulAut.conj (Steinberg.x p a)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨q,b,hqk,hq,rfl⟩
    exact level_conjugate_triangular_root height k p hp a q hqk hq b
  exact H hg

theorem level_root_normalizes (height : Fin n→ℕ) (k : ℕ)
    (p : Root n) (hp : height p.row=height p.col) (a : R) :
    Steinberg.x p a∈Subgroup.normalizer (triangular (R:=R) height k : Set (Steinberg n R)) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · exact level_conjugate_triangular height k p hp a
  · intro hx
    have hx' := level_conjugate_triangular height k p hp (-a) hx
    simpa only [Steinberg.x_neg,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hx'
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
lemma diagonalBlockHom_eq (p : Root n) : diagonalBlockHom (N:=N) (R:=R) p=copyRoots p := by
  apply MonoidHom.pi_ext
  intro s a
  have he : (fun t : Fin N=>((Pi.mulSingle s a : Fin N→Multiplicative R) t).toAdd)=Pi.single s a.toAdd := by
    funext t
    by_cases ht : t=s <;> simp [ht]
  change blockRoot p (Matrix.diagonal (fun t=>((Pi.mulSingle s a : Fin N→Multiplicative R) t).toAdd))=copyRoots p (Pi.mulSingle s a)
  rw [he,Matrix.diagonal_single,blockRoot_single]
  exact (MonoidHom.noncommPiCoprod_mulSingle
    (fun s=>(copyMap (n:=n) (R:=R) s).comp (rootHom p)) s a).symm
lemma diagonalCopy_x (p : Root n) (a : R) :
    diagonalCopy (N:=N) (Steinberg.x p a)=blockRoot p (Matrix.diagonal (fun _=>a)) := by
  have he := DFunLike.congr_fun (diagonalBlockHom_eq (N:=N) (R:=R) p) (fun _=>Multiplicative.ofAdd a)
  exact he.symm
lemma upper_faithful {g : Steinberg (n*N) R} (hg : g∈upper) (hmat : Elementary.representation g=1) : g=1 :=
  triangular_faithful innerHeight N (fun i=>(finProdFinEquiv.symm i).2.isLt) hg hmat
lemma strict_block_mem_upper (p : Root n) (A : Matrix (Fin N) (Fin N) R)
    (hA : ∀ s t, t ≤ s → A s t = 0) : blockRoot p A∈upper := by
  change Finset.noncommProd Finset.univ
    (fun st : Fin N×Fin N=>Steinberg.x (blockPosition p st) (A st.1 st.2))
    (fun st _ uv _ _=>block_factors_commute p st uv _ _)∈upper
  apply Subgroup.noncommProd_mem
  intro st _
  by_cases ht : st.1 < st.2
  · apply Subgroup.subset_closure
    refine ⟨blockPosition p st,A st.1 st.2,by omega,?_,rfl⟩
    simpa only [blockPosition,innerHeight_blockIndex] using (show st.1.val < st.2.val from ht)
  · rw [hA _ _ (le_of_not_gt ht),Steinberg.x_zero]
    exact Subgroup.one_mem _
lemma diagonalCopy_normalizes (u : Steinberg n R) :
    diagonalCopy (N:=N) u∈Subgroup.normalizer (upper (n:=n) (N:=N) (R:=R) : Set (Steinberg (n*N) R)) := by
  have he : (⊤ : Subgroup (Steinberg n R))≤
      (Subgroup.normalizer (upper (n:=n) (N:=N) (R:=R) : Set (Steinberg (n*N) R))).comap diagonalCopy := by
    rw [←Steinberg.closure_range_x]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨p,a⟩,rfl⟩
    change diagonalCopy (N:=N) (Steinberg.x p a)∈Subgroup.normalizer (upper (n:=n) (N:=N) (R:=R) : Set (Steinberg (n*N) R))
    change Finset.noncommProd Finset.univ
      (fun s : Fin N=>copyMap s (Steinberg.x p a))
      (fun s _ t _ h=>copy_commute h _ _)∈Subgroup.normalizer (upper (n:=n) (N:=N) (R:=R) : Set (Steinberg (n*N) R))
    apply Subgroup.noncommProd_mem
    intro s _
    change Steinberg.x (blockPosition p (s,s)) a∈_
    apply level_root_normalizes innerHeight 0
    simp only [blockPosition,innerHeight_blockIndex]
  exact he (Subgroup.mem_top u)
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]
lemma matrixSteinbergEval_kernel (T : Matrix (Fin N) (Fin N) (ZMod 2))
    (u : Steinberg n (Polynomial R)) (hu : Elementary.representation u=1) :
    Elementary.representation (matrixSteinbergEval T u)=1 := by
  exact blockMap_kernel (n:=n) (N:=N) (R:=R) _
    (Elementary.map_kernel (n:=n) (R:=Polynomial R) (S:=Matrix (Fin N) (Fin N) R) (matrixEvalRingHom T) u hu)
lemma scalarEval_kernel (c : ZMod 2) (u : Steinberg n (Polynomial R))
    (hu : Elementary.representation u=1) : Elementary.representation (Steinberg.map (scalarEval c) u)=1 :=
  Elementary.map_kernel (scalarEval c) u hu
lemma numeric_upper {T : Matrix (Fin N) (Fin N) (ZMod 2)} (hT : T.IsUpperTriangular) :
    (numericMatrix (R:=R) T).IsUpperTriangular := by
  intro i j hji
  change algebraMap (ZMod 2) R (T i j)=0
  rw [hT hji,map_zero]
omit [Algebra (ZMod 2) R] in
lemma triangular_mul_diag {A B : Matrix (Fin N) (Fin N) R}
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (s : Fin N) :
    (A*B) s s=A s s*B s s := by
  rw [Matrix.mul_apply,Finset.sum_eq_single s]
  · intro t _ hts
    rcases lt_or_gt_of_ne hts with hts|hst
    · rw [hA hts,zero_mul]
    · rw [hB hst,mul_zero]
  · simp
omit [Algebra (ZMod 2) R] in
lemma triangular_pow_diag {A : Matrix (Fin N) (Fin N) R} (hA : A.IsUpperTriangular)
    (m : ℕ) (s : Fin N) : (A^m) s s=(A s s)^m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ,triangular_mul_diag (hA.pow m) hA,ih,pow_succ]
lemma matrixEval_upper {T : Matrix (Fin N) (Fin N) (ZMod 2)} (hT : T.IsUpperTriangular)
    (a : Polynomial R) : (matrixEval T a).IsUpperTriangular := by
  induction a using Polynomial.induction_on' with
  | add a b ha hb => rw [map_add];exact ha.add hb
  | monomial m a =>
    change (Polynomial.eval₂ (Matrix.scalar (Fin N)) (numericMatrix T) (Polynomial.monomial m a)).IsUpperTriangular
    rw [Polynomial.eval₂_monomial,Matrix.scalar_apply]
    exact (Matrix.blockTriangular_diagonal _).mul ((numeric_upper hT).pow m)
lemma matrixEval_diag {T : Matrix (Fin N) (Fin N) (ZMod 2)} (hT : T.IsUpperTriangular)
    (c : ZMod 2) (hd : ∀ s,T s s=c) (a : Polynomial R) (s : Fin N) :
    matrixEval T a s s=scalarEval c a := by
  induction a using Polynomial.induction_on' with
  | add a b ha hb => simp only [map_add,Matrix.add_apply,ha,hb]
  | monomial m a =>
    change Polynomial.eval₂ (Matrix.scalar (Fin N)) (numericMatrix T) (Polynomial.monomial m a) s s=
      Polynomial.eval₂ (RingHom.id R) (algebraMap (ZMod 2) R c) (Polynomial.monomial m a)
    rw [Polynomial.eval₂_monomial,Polynomial.eval₂_monomial,Matrix.scalar_apply,Matrix.diagonal_mul,
      triangular_pow_diag (numeric_upper hT)]
    change a*(algebraMap (ZMod 2) R (T s s))^m=a*(algebraMap (ZMod 2) R c)^m
    rw [hd]
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
lemma diagonalCopy_eq : diagonalCopy (n:=n) (N:=N) (R:=R)=
    blockMap.comp (Steinberg.map scalarRingHom) := by
  apply Steinberg.hom_ext
  intro p a
  rw [diagonalCopy_x,MonoidHom.comp_apply,Steinberg.map_x,blockMap_x]
  rfl
lemma diagonalCopy_kernel (u : Steinberg n R) (hu : Elementary.representation u=1) :
    Elementary.representation (diagonalCopy (N:=N) u)=1 := by
  rw [diagonalCopy_eq]
  exact blockMap_kernel (n:=n) (N:=N) (R:=R) _
    (Elementary.map_kernel (n:=n) (R:=R) (S:=Matrix (Fin N) (Fin N) R) scalarRingHom u hu)
variable [Algebra (ZMod 2) R]
lemma triangular_entry_split {T : Matrix (Fin N) (Fin N) (ZMod 2)}
    (hT : T.IsUpperTriangular) (c : ZMod 2) (hd : ∀s,T s s=c)
    (p : Root n) (a : Polynomial R) :
    ∃z∈upper (n:=n) (N:=N) (R:=R),
      matrixSteinbergEval T (Steinberg.x p a)=
        diagonalCopy (N:=N) (Steinberg.map (scalarEval c) (Steinberg.x p a))*z := by
  let D : Matrix (Fin N) (Fin N) R := Matrix.diagonal (fun _=>scalarEval c a)
  let B : Matrix (Fin N) (Fin N) R := matrixEval T a-D
  refine ⟨blockRoot p B,?_,?_⟩
  · apply strict_block_mem_upper
    intro s t hts
    rcases eq_or_lt_of_le hts with he|ht
    · subst t
      simp only [B,D,Matrix.sub_apply,Matrix.diagonal_apply_eq,matrixEval_diag hT c hd,sub_self]
    · have hne : s≠t := (ne_of_lt ht).symm
      simp only [B,D,Matrix.sub_apply,matrixEval_upper hT a ht,Matrix.diagonal_apply_ne _ hne,sub_self]
  · rw [Steinberg.map_x,diagonalCopy_x]
    rw [matrixSteinbergEval,MonoidHom.comp_apply,Steinberg.map_x,blockMap_x]
    change blockRoot p (matrixEval T a)=blockRoot p D*blockRoot p B
    rw [←blockRoot_add]
    congr 1
    dsimp [B]
    abel
lemma triangular_collect {T : Matrix (Fin N) (Fin N) (ZMod 2)}
    (hT : T.IsUpperTriangular) (c : ZMod 2) (hd : ∀s,T s s=c)
    (u : Steinberg n (Polynomial R)) :
    ∃z∈upper (n:=n) (N:=N) (R:=R),matrixSteinbergEval T u=
      diagonalCopy (N:=N) (Steinberg.map (scalarEval c) u)*z := by
  have hu : u∈Subgroup.closure (Set.range (fun pa : Root n×Polynomial R=>Steinberg.x pa.1 pa.2)) := by
    rw [Steinberg.closure_range_x]
    exact Subgroup.mem_top u
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨⟨p,a⟩,rfl⟩:=hu
    exact triangular_entry_split hT c hd p a
  | one => exact ⟨1,Subgroup.one_mem _,by simp⟩
  | mul u v hu hv ihu ihv =>
    obtain ⟨z,hz,hez⟩:=ihu
    obtain ⟨w,hw,hew⟩:=ihv
    let d := diagonalCopy (N:=N) (Steinberg.map (scalarEval c) v)
    have hn : d⁻¹∈Subgroup.normalizer (upper (n:=n) (N:=N) (R:=R) : Set (Steinberg (n*N) R)) :=
      Subgroup.inv_mem _ (diagonalCopy_normalizes _)
    have hc : d⁻¹*z*d∈upper := by
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hn z).mp hz
    refine ⟨(d⁻¹*z*d)*w,Subgroup.mul_mem _ hc hw,?_⟩
    simp only [map_mul,hez,hew]
    dsimp [d]
    group
  | inv u hu ihu =>
    obtain ⟨z,hz,hez⟩:=ihu
    let d := diagonalCopy (N:=N) (Steinberg.map (scalarEval c) u)
    have hc : d*z⁻¹*d⁻¹∈upper :=
      (Subgroup.mem_normalizer_iff.mp (diagonalCopy_normalizes _) z⁻¹).mp (Subgroup.inv_mem _ hz)
    refine ⟨d*z⁻¹*d⁻¹,hc,?_⟩
    simp only [map_inv,hez]
    dsimp [d]
    group

theorem triangular_evaluation {T : Matrix (Fin N) (Fin N) (ZMod 2)}
    (hT : T.IsUpperTriangular) (c : ZMod 2) (hd : ∀s,T s s=c)
    (u : Steinberg n (Polynomial R)) (hu : Elementary.representation u=1) :
    matrixSteinbergEval T u=diagonalCopy (N:=N) (Steinberg.map (scalarEval c) u) := by
  obtain ⟨z,hz,he⟩ := triangular_collect hT c hd u
  have hf := matrixSteinbergEval_kernel (R:=R) T u hu
  have hg := diagonalCopy_kernel (N:=N) _ (scalarEval_kernel c u hu)
  have hm := congrArg Elementary.representation he
  rw [map_mul,hg,one_mul,hf] at hm
  have hz1 := upper_faithful hz hm.symm
  simpa only [hz1,mul_one] using he
end
end SourceBurnside.Kernel

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_CoefficientQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside
namespace FiniteSteinbergPresentation
open MonomialCompletion
variable {n : ℕ} {α : Type u}

instance finitelyPresented [Finite α] : Group.IsFinitelyPresented (Group n α) := by
  have : Finite {r | Rel n α r} := (rel_finite (n := n) (α := α)).to_subtype
  infer_instance

 theorem free_finitelyPresented [Finite α] (hn : 5 ≤ n) :
    _root_.Group.IsFinitelyPresented (Steinberg n (Polynomial α)) :=
  _root_.Group.IsFinitelyPresented.equiv (equiv hn)

end FiniteSteinbergPresentation

namespace SteinbergQuotient

variable {n : ℕ} {R : Type u} [Ring R]

variable (S : Set R)

 theorem rootRelations_finite (hS : S.Finite) : (rootRelations (n := n) S).Finite := by
  have h : rootRelations (n := n) S =
      (fun z : Root n × R => Steinberg.x z.1 z.2) '' (Set.univ ×ˢ S) := by
    ext g
    constructor
    · rintro ⟨p, a, ha, rfl⟩
      exact ⟨(p, a), ⟨Set.mem_univ _, ha⟩, rfl⟩
    · rintro ⟨⟨p, a⟩, ⟨_, ha⟩, rfl⟩
      exact ⟨p, a, ha, rfl⟩
  rw [h]
  exact ((Set.finite_univ : (Set.univ : Set (Root n)).Finite).prod hS).image _

 theorem normal_finitelyGenerated (hS : S.Finite) :
    (normal (n := n) S).IsFinitelyNormallyGenerated :=
  ⟨rootRelations S, rootRelations_finite S hS, rfl⟩

 theorem finitelyPresented (hn : 5 ≤ n) (hS : S.Finite)
    [Group.IsFinitelyPresented (Steinberg n R)] :
    Group.IsFinitelyPresented (Steinberg n (Coeff S)) := by
  have : Group.IsFinitelyPresented (Quot (n := n) S) :=
    Group.IsFinitelyPresented.quotient (normal S) (normal_finitelyGenerated S hS)
  exact Group.IsFinitelyPresented.equiv (equiv S hn)

end SteinbergQuotient

theorem steinberg_finitelyPresented {n : ℕ} (hn : 5 ≤ n) {α : Type u} [Finite α]
    (S : Set (MonomialCompletion.Polynomial α)) (hS : S.Finite) :
    Group.IsFinitelyPresented (Steinberg n (SteinbergQuotient.Coeff S)) := by
  have : Group.IsFinitelyPresented (Steinberg n (MonomialCompletion.Polynomial α)) :=
    FiniteSteinbergPresentation.free_finitelyPresented hn
  exact SteinbergQuotient.finitelyPresented S hn hS

end SourceBurnside

namespace SourceBurnside.WordAlgebra.Table
noncomputable section
open Classical
variable {α K : Type*} [CommRing K]
lemma quotient_smul (T : Table α) (k : K) (p : Polynomial K α) : T.quotient (k • p)=k • T.quotient p :=
  map_smul (RingCon.mkₐ K (T.ideal (K:=K)).ringCon) k p

end
end SourceBurnside.WordAlgebra.Table

namespace SourceBurnside.FiniteTable.Codec
noncomputable section
open Classical WordAlgebra
variable {h d : ℕ} {hh : 0<h} {S : Schedule (2^h)}
lemma finite_boundedWords (h n : ℕ) : (boundedWords h n).Finite := Set.finite_range _
lemma mem_boundedWords (w : FreeMonoid (Raw h)) {n : ℕ} (hw : w.toList.length ≤ n) :
    w∈boundedWords h n := by
  refine ⟨⟨⟨w.toList.length,by omega⟩,w.toList.get⟩,?_⟩
  simp

lemma finite_algebraTable_relations (h4 : 4 ≤ h) (K : Type*) [Ring K] :
    ((algebraTable hh S d).relations (K:=K)).Finite := by
  have hr : {vw : FreeMonoid (Raw h) × FreeMonoid (Raw h) | (algebraTable hh S d).rep vw.1 vw.2}.Finite := by
    apply ((finite_boundedWords h 2).prod (finite_boundedWords h 2)).subset
    rintro ⟨v,w⟩ hvw
    obtain ⟨hl,hn,hk⟩ := replacement_lengths h4 S d v.toList w.toList hvw
    exact ⟨mem_boundedWords v hk,mem_boundedWords w (hl ▸ hk)⟩
  have hz : (algebraTable hh S d).zero.Finite := by
    apply (finite_boundedWords h 2).subset
    intro w hw
    exact mem_boundedWords w (zero_lengths hh S d w.toList hw).2
  let f : FreeMonoid (Raw h) × FreeMonoid (Raw h) → WordAlgebra.Polynomial K (Raw h) :=
    fun vw => monomial vw.1 - monomial vw.2
  apply ((hr.image f).union (hz.image (monomial (K:=K)))).subset
  rintro p (⟨v,w,hvw,rfl⟩ | ⟨w,hw,rfl⟩)
  · exact Or.inl ⟨(v,w),hvw,rfl⟩
  · exact Or.inr ⟨w,hw,rfl⟩
end
end SourceBurnside.FiniteTable.Codec
namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open FiniteTable
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)

theorem steinberg_finitely_presented {h : ℕ} (hh : A.threshold ≤ h) :
    Group.IsFinitelyPresented (Steinberg 12 (A.Algebra (ZMod 2) h hh)) :=
  steinberg_finitelyPresented (by decide) (A.table h hh).relations
    (Codec.finite_algebraTable_relations (A.threshold_four.trans hh) _)
end
end SourceBurnside.SourceMachine.MachineHierarchy

namespace SourceBurnside.ConcreteSource
noncomputable section

theorem steinberg_finitely_presented : Group.IsFinitelyPresented (Steinberg 12 R) :=
  machine.steinberg_finitely_presented (by rfl)
end
end SourceBurnside.ConcreteSource

namespace SourceBurnside.WordAlgebra.Table
noncomputable section
open Classical
variable {α K : Type*} [CommRing K]

lemma algHom_ext_word (T : Table α) {S : Type*} [Semiring S] [_root_.Algebra K S]
    (f g : T.Algebra (K:=K) →ₐ[K] S) (hw : ∀w,f (T.word w)=g (T.word w)) : f=g := by
  apply AlgHom.ext
  intro x
  obtain ⟨p,rfl⟩ := (T.ideal (K:=K)).ringCon.mk'_surjective x
  induction p using MonoidAlgebra.induction_on with
  | of w => exact hw w
  | add p q hp hq => simpa only [map_add] using congrArg₂ (fun a b : S=>a+b) hp hq
  | smul k p hp =>
    change f (T.quotient (k • p))=g (T.quotient (k • p))
    rw [quotient_smul,map_smul,map_smul,hp]

lemma evalOne_gradingHom (T : Table α) (hh : T.Homogeneous) :
    T.evalOne.comp (T.gradingHom (K:=K) hh)=AlgHom.id K _ := by
  apply T.algHom_ext_word
  intro w
  simp [evalOne,_root_.Polynomial.eval₂AlgHom_apply,_root_.Polynomial.eval₂_monomial]
lemma evalZero_gradingHom (T : Table α) (hh : T.Homogeneous) (hz : ∀z∈T.zero,z≠1) :
    T.evalZero.comp (T.gradingHom (K:=K) hh)=(Algebra.ofId K _).comp (T.augmentation hh hz) := by
  apply T.algHom_ext_word
  intro w
  by_cases hw : w=1
  · simp [hw,evalZero,_root_.Polynomial.eval₂AlgHom_apply]
  · have hl : w.length≠0 := fun h=>hw (FreeMonoid.length_eq_zero.mp h)
    simp [evalZero,_root_.Polynomial.eval₂AlgHom_apply,_root_.Polynomial.eval₂_monomial,hl]
end
end SourceBurnside.WordAlgebra.Table

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_BandFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
lemma left_conjugate_strip_root (H L : Finset (Fin n)) (hd : Disjoint H L)
    (p : Root n) (hr : p.row∈H) (hc : p.col∈H) (a : R)
    (q : RectIndex H L) (b : R) :
    Steinberg.x p a*Steinberg.x (rectPosition H L hd q) b*(Steinberg.x p a)⁻¹∈Strip H L hd := by
  have hrow : p.row≠q.2.val := fun he=>Finset.disjoint_left.mp hd hr (he.symm ▸ q.2.property)
  by_cases he : p.col=q.1.val
  · have hp : p=⟨p.row,q.1.val,he ▸ p.ne⟩ := by cases p;cases he;rfl
    rw [hp]
    dsimp only [rectPosition]
    rw [Steinberg.conjugate_chain p.row q.1.val q.2.val (he ▸ p.ne) (rectPosition H L hd q).ne hrow a b]
    apply (Strip H L hd).mul_mem
    · exact Subgroup.subset_closure ⟨(⟨p.row,hr⟩,q.2),a*b,rfl⟩
    · exact Subgroup.subset_closure ⟨q,b,rfl⟩
  · rw [Steinberg.conjugate_commute p (rectPosition H L hd q) he hrow]
    exact Subgroup.subset_closure ⟨q,b,rfl⟩
lemma left_conjugate_strip (H L : Finset (Fin n)) (hd : Disjoint H L)
    (p : Root n) (hr : p.row∈H) (hc : p.col∈H) (a : R)
    {g : Steinberg n R} (hg : g∈Strip H L hd) :
    Steinberg.x p a*g*(Steinberg.x p a)⁻¹∈Strip H L hd := by
  have Hle : Strip H L hd ≤ (Strip H L hd).comap (MulAut.conj (Steinberg.x p a)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨q,b,rfl⟩
    exact left_conjugate_strip_root H L hd p hr hc a q b
  exact Hle hg
lemma side_root_normalizes (H L : Finset (Fin n)) (hd : Disjoint H L)
    (p : Root n) (h : (p.row∈H ∧ p.col∈H) ∨ (p.row∈L ∧ p.col∈L)) (a : R) :
    Steinberg.x p a∈Subgroup.normalizer (Strip (R:=R) H L hd : Set (Steinberg n R)) := by
  have hh (b : R) {g : Steinberg n R} (hg : g∈Strip H L hd) :
      Steinberg.x p b*g*(Steinberg.x p b)⁻¹∈Strip H L hd := by
    rcases h with ⟨hr,hc⟩|⟨hr,hc⟩
    · exact left_conjugate_strip H L hd p hr hc b hg
    · exact right_conjugate_strip H L hd p hr hc b hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  constructor
  · exact hh a
  · intro hg
    have he := hh (-a) hg
    simp only [Steinberg.x_neg,inv_inv] at he
    simpa [mul_assoc] using he
lemma strip_mono {H L H' L' : Finset (Fin n)} (hd : Disjoint H L) (hd' : Disjoint H' L')
    (hH : H⊆H') (hL : L⊆L') : Strip (R:=R) H L hd≤Strip H' L' hd' := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨q,a,rfl⟩
  exact Subgroup.subset_closure ⟨(⟨q.1.val,hH q.1.property⟩,⟨q.2.val,hL q.2.property⟩),a,rfl⟩
lemma blockRoot_mem_subgroup (p : Root n) (A : Matrix (Fin N) (Fin N) R)
    (S : Subgroup (Steinberg (n*N) R))
    (h : ∀s t,Steinberg.x (blockPosition p (s,t)) (A s t)∈S) : blockRoot p A∈S := by
  change Finset.noncommProd Finset.univ
    (fun st : Fin N×Fin N=>Steinberg.x (blockPosition p st) (A st.1 st.2))
    (fun st _ uv _ _=>block_factors_commute p st uv _ _)∈S
  apply Subgroup.noncommProd_mem
  intro st _
  exact h st.1 st.2
lemma blockRoot_commutes_element (p : Root n) (A : Matrix (Fin N) (Fin N) R)
    (g : Steinberg (n*N) R)
    (h : ∀s t,Commute (Steinberg.x (blockPosition p (s,t)) (A s t)) g) :
    Commute (blockRoot p A) g := by
  change Commute (Finset.noncommProd Finset.univ
    (fun st : Fin N×Fin N=>Steinberg.x (blockPosition p st) (A st.1 st.2))
    (fun st _ uv _ _=>block_factors_commute p st uv _ _)) g
  exact (Finset.noncommProd_commute _ _ _ g (fun st _=>(h st.1 st.2).symm)).symm

theorem block_conjugate_strip
    (H L H' L' : Finset (Fin (n*N))) (hd : Disjoint H L) (hd' : Disjoint H' L')
    (hH : H⊆H') (hL : L⊆L') (p : Root n) (A : Matrix (Fin N) (Fin N) R)
    (hsource : ∀s t,A s t≠0→blockIndex p.col t∈H→blockIndex p.row s∈H')
    (htarget : ∀s t,A s t≠0→blockIndex p.row s∈L→blockIndex p.col t∈L')
    {g : Steinberg (n*N) R} (hg : g∈Strip H L hd) :
    blockRoot p A*g*(blockRoot p A)⁻¹∈Strip H' L' hd' := by
  let near (s t : Fin N) : Prop :=
    (blockIndex p.row s∈H' ∧ blockIndex p.col t∈H') ∨
    (blockIndex p.row s∈L' ∧ blockIndex p.col t∈L')
  let B : Matrix (Fin N) (Fin N) R := fun s t=>if near s t then A s t else 0
  let C : Matrix (Fin N) (Fin N) R := fun s t=>if near s t then 0 else A s t
  have hs : A=B+C := by ext s t;change A s t=(if near s t then A s t else 0)+(if near s t then 0 else A s t);split_ifs <;> simp
  have hB : blockRoot p B∈Subgroup.normalizer (Strip (R:=R) H' L' hd' : Set (Steinberg (n*N) R)) := by
    apply blockRoot_mem_subgroup
    intro s t
    by_cases hn : near s t
    · change Steinberg.x (blockPosition p (s,t)) (if near s t then A s t else 0)∈_
      rw [ite_eq_left hn]
      exact side_root_normalizes H' L' hd' _ hn _
    · change Steinberg.x (blockPosition p (s,t)) (if near s t then A s t else 0)∈_
      rw [ite_eq_right hn,Steinberg.x_zero]
      exact Subgroup.one_mem _
  have hCroot (q : RectIndex H L) (a : R) :
      Commute (blockRoot p C) (Steinberg.x (rectPosition H L hd q) a) := by
    apply blockRoot_commutes_element
    intro s t
    by_cases hn : near s t
    · simp only [C,ite_eq_left hn,Steinberg.x_zero,Commute.one_left]
    · by_cases hz : A s t=0
      · simp only [C,ite_eq_right hn,hz,Steinberg.x_zero,Commute.one_left]
      · change Commute (Steinberg.x (blockPosition p (s,t)) (if near s t then 0 else A s t)) _
        rw [ite_eq_right hn]
        apply Steinberg.x_commute
        · intro he
          change blockIndex p.col t=q.1.val at he
          have ht : blockIndex p.col t∈H := he.symm ▸ q.1.property
          exact hn (Or.inl ⟨hsource s t hz ht,hH ht⟩)
        · intro he
          change blockIndex p.row s=q.2.val at he
          have hr : blockIndex p.row s∈L := he.symm ▸ q.2.property
          exact hn (Or.inr ⟨hL hr,htarget s t hz hr⟩)
  have hC : blockRoot p C*g*(blockRoot p C)⁻¹=g := by
    have he : Strip H L hd≤(MulAut.conj (blockRoot p C)).toMonoidHom.eqLocus (MonoidHom.id _) := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨q,a,rfl⟩
      exact CommutatorCalculus.conj_of_commute (hCroot q a)
    exact he hg
  rw [hs,blockRoot_add,mul_inv_rev]
  have he : blockRoot p B*blockRoot p C*g*((blockRoot p C)⁻¹*(blockRoot p B)⁻¹)=
      blockRoot p B*(blockRoot p C*g*(blockRoot p C)⁻¹)*(blockRoot p B)⁻¹ := by group
  rw [he,hC]
  exact (Subgroup.mem_normalizer_iff.mp hB g).mp (strip_mono hd hd' hH hL hg)
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
lemma highBand_mono {v w : ℕ} (h : v ≤ w) : highBand (n:=n) (N:=N) v⊆highBand w := by
  intro i hi
  simp only [highBand,Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
  omega
lemma lowBand_mono {v w : ℕ} (h : v ≤ w) : lowBand (n:=n) (N:=N) v⊆lowBand w := by
  intro i hi
  simp only [lowBand,Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
  omega
lemma bandStrip_mono {v w : ℕ} (hv : 2*v ≤ N) (hw : 2*w ≤ N) (h : v ≤ w) :
    bandStrip (n:=n) (R:=R) v hv ≤ bandStrip w hw :=
  strip_mono _ _ (highBand_mono h) (lowBand_mono h)
lemma blockRoot_neg (p : Root n) (A : Matrix (Fin N) (Fin N) R) :
    blockRoot p (-A)=(blockRoot p A)⁻¹ := map_inv (blockHom p) _

lemma band_transport (d w : ℕ) (h : 2*(w+d) ≤ N) (hw : 2*w ≤ N)
    (p : Root n) (A : Matrix (Fin N) (Fin N) R)
    (hA : ∀s t,A s t≠0→t.val ≤ s.val+d)
    {g : Steinberg (n*N) R} (hg : g∈bandStrip w hw) :
    blockRoot p A*g*(blockRoot p A)⁻¹∈bandStrip (w+d) h := by
  apply block_conjugate_strip (highBand w) (lowBand w) (highBand (w+d)) (lowBand (w+d))
    (bands_disjoint w hw) (bands_disjoint (w+d) h)
    (highBand_mono (Nat.le_add_right _ _)) (lowBand_mono (Nat.le_add_right _ _)) p A _ _ hg
  · intro s t hst ht
    simp only [highBand,Finset.mem_filter,Finset.mem_univ,true_and,innerHeight_blockIndex] at ht ⊢
    have := hA s t hst
    omega
  · intro s t hst hs
    simp only [lowBand,Finset.mem_filter,Finset.mem_univ,true_and,innerHeight_blockIndex] at hs ⊢
    have := hA s t hst
    omega
lemma wrap_block_mem (d : ℕ) (h : 2*d ≤ N) (p : Root n) (B : Matrix (Fin N) (Fin N) R)
    (hB : ∀s t,B s t≠0→N ≤ s.val+d ∧ t.val<d) : blockRoot p B∈bandStrip d h := by
  apply blockRoot_mem_subgroup
  intro s t
  by_cases hb : B s t=0
  · rw [hb,Steinberg.x_zero];exact Subgroup.one_mem _
  · have he := hB s t hb
    have hs : blockIndex p.row s∈highBand (n:=n) d := by simpa [highBand] using he.1
    have ht : blockIndex p.col t∈lowBand (n:=n) d := by simpa [lowBand] using he.2
    exact Subgroup.subset_closure ⟨(⟨_,hs⟩,⟨_,ht⟩),B s t,rfl⟩

theorem band_wrap_collect (d : ℕ) (l : List (BlockFactor n N R)) :
    (∀x∈l,x.Bounded d)→∀(h : 2*((l.length+1)*d) ≤ N),
    ∃z∈bandStrip ((l.length+1)*d) h,wrappedProduct l=truncatedProduct l*z := by
  induction l using List.reverseRecOn with
  | nil =>
    intro hl h
    exact ⟨1,Subgroup.one_mem _,by simp [wrappedProduct,truncatedProduct]⟩
  | append_singleton l x ih =>
    intro hl h
    have h' : 2*((l.length+1)*d+d) ≤ N := by
      simp only [List.length_append,List.length_singleton] at h
      convert h using 1 <;> first | rfl | ring
    have hp : 2*((l.length+1)*d) ≤ N := by omega
    have hx := hl x (by simp)
    obtain ⟨z,hz,he⟩ := ih (fun y hy=>hl y (List.mem_append_left _ hy)) hp
    have hneg : ∀s t,(-x.main) s t≠0→t.val ≤ s.val+d := by
      intro s t ht
      exact hx.1 s t (fun hz=>ht (by simp [hz]))
    have hc := band_transport d ((l.length+1)*d) h' hp x.position (-x.main) hneg hz
    rw [blockRoot_neg,inv_inv] at hc
    have hd : 2*d ≤ N := by nlinarith [Nat.zero_le (l.length*d)]
    have hf0 := wrap_block_mem d hd x.position x.correction hx.2
    have hwidth : d ≤ (l.length+1)*d+d := by omega
    have hf := bandStrip_mono hd h' hwidth hf0
    refine ⟨((blockRoot x.position x.main)⁻¹*z*blockRoot x.position x.main)*blockRoot x.position x.correction,?_,?_⟩
    · have hm := Subgroup.mul_mem _ hc hf
      simpa only [List.length_append,List.length_singleton,Nat.add_mul,Nat.one_mul,add_assoc] using hm
    · simp only [wrappedProduct,truncatedProduct,List.map_append,List.map_cons,List.map_nil,
        List.prod_append,List.prod_cons,List.prod_nil,mul_one] at he ⊢
      rw [he,blockRoot_add]
      group

theorem band_wrap_removal (d : ℕ) (l : List (BlockFactor n N R))
    (hl : ∀x∈l,x.Bounded d) (h : 2*((l.length+1)*d) ≤ N)
    (hW : Elementary.representation (wrappedProduct l)=1)
    (hD : Elementary.representation (truncatedProduct l)=1) :
    wrappedProduct l=truncatedProduct l := by
  obtain ⟨z,hz,he⟩ := band_wrap_collect d l hl h
  have hm := congrArg Elementary.representation he
  rw [map_mul,hD,one_mul,hW] at hm
  have hz1 := strip_faithful (highBand ((l.length+1)*d)) (lowBand ((l.length+1)*d))
    (bands_disjoint _ h) hz hm.symm
  simpa only [hz1,mul_one] using he
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {N : ℕ} {R : Type*} [Ring R]

lemma truncatedShift_pow (b : ℕ) (s t : Fin N) :
    (truncatedShift N R^b) s t=if s.val+b=t.val then 1 else 0 := by
  induction b generalizing s t with
  | zero => simp [Matrix.one_apply,Fin.ext_iff]
  | succ b ih =>
    rw [pow_succ,Matrix.mul_apply]
    simp only [ih,truncatedShift]
    by_cases h : s.val+b<N
    · let k : Fin N := ⟨s.val+b,h⟩
      rw [Finset.sum_eq_single k]
      · simp [k,add_assoc]
      · intro u _ huk
        have he : s.val+b≠u.val := by intro he;apply huk;apply Fin.ext;exact he.symm
        simp only [ite_eq_right he,zero_mul]
      · simp
    · have hr : s.val+(b+1)≠t.val := by have := t.isLt;omega
      rw [ite_eq_right hr]
      apply Finset.sum_eq_zero
      intro u _
      have he : s.val+b≠u.val := by have := u.isLt;omega
      simp only [ite_eq_right he,zero_mul]
lemma cyclicShift_pow (hN : 0<N) (b : ℕ) (s t : Fin N) :
    (cyclicShift N R^b) s t=if (s.val+b)%N=t.val then 1 else 0 := by
  induction b generalizing s t with
  | zero => simp [Matrix.one_apply,Fin.ext_iff,Nat.mod_eq_of_lt s.isLt]
  | succ b ih =>
    rw [pow_succ,Matrix.mul_apply]
    simp only [ih,cyclicShift]
    let k : Fin N := ⟨(s.val+b)%N,Nat.mod_lt _ hN⟩
    rw [Finset.sum_eq_single k]
    · simp only [k]
      have he : ((s.val+b)%N+1)%N=(s.val+(b+1))%N := by
        rw [Nat.mod_add_mod,add_assoc]
      rw [he]
      simp
    · intro u _ huk
      have he : (s.val+b)%N≠u.val := by intro he;apply huk;apply Fin.ext;exact he.symm
      simp only [ite_eq_right he,zero_mul]
    · simp
lemma truncatedShift_upper : (truncatedShift N R).IsUpperTriangular := by
  intro s t hts
  have he : s.val+1≠t.val := by change t.val < s.val at hts;omega
  exact ite_eq_right he
lemma truncatedShift_diag (s : Fin N) : truncatedShift N R s s=0 := by
  exact ite_eq_right (by omega)
variable [Algebra (ZMod 2) R]
lemma numeric_truncatedShift : numericMatrix (R:=R) (truncatedShift N (ZMod 2))=truncatedShift N R := by
  ext s t
  change algebraMap (ZMod 2) R (if s.val+1=t.val then 1 else 0)=(if s.val+1=t.val then 1 else 0)
  split_ifs <;> simp
lemma numeric_cyclicShift : numericMatrix (R:=R) (cyclicShift N (ZMod 2))=cyclicShift N R := by
  ext s t
  change algebraMap (ZMod 2) R (if (s.val+1)%N=t.val then 1 else 0)=(if (s.val+1)%N=t.val then 1 else 0)
  split_ifs <;> simp
lemma truncated_eval_monomial (b : ℕ) (a : R) (s t : Fin N) :
    matrixEval (truncatedShift N (ZMod 2)) (Polynomial.monomial b a) s t=
      if s.val+b=t.val then a else 0 := by
  change Polynomial.eval₂ (Matrix.scalar (Fin N)) (numericMatrix (truncatedShift N (ZMod 2)))
    (Polynomial.monomial b a) s t=_
  rw [Polynomial.eval₂_monomial,Matrix.scalar_apply,Matrix.diagonal_mul,numeric_truncatedShift,truncatedShift_pow]
  split_ifs <;> simp
lemma cyclic_eval_monomial (hN : 0<N) (b : ℕ) (a : R) (s t : Fin N) :
    matrixEval (cyclicShift N (ZMod 2)) (Polynomial.monomial b a) s t=
      if (s.val+b)%N=t.val then a else 0 := by
  change Polynomial.eval₂ (Matrix.scalar (Fin N)) (numericMatrix (cyclicShift N (ZMod 2)))
    (Polynomial.monomial b a) s t=_
  rw [Polynomial.eval₂_monomial,Matrix.scalar_apply,Matrix.diagonal_mul,numeric_cyclicShift,cyclicShift_pow hN]
  split_ifs <;> simp
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]
lemma truncated_eval_outside (d : ℕ) (a : Polynomial R) (ha : a.natDegree ≤ d)
    (s t : Fin N) (hst : s.val+d<t.val) :
    matrixEval (truncatedShift N (ZMod 2)) a s t=0 := by
  conv_lhs => rw [a.as_sum_support,map_sum,Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro b hb
  rw [truncated_eval_monomial]
  have hb' := (Polynomial.le_natDegree_of_mem_supp b hb).trans ha
  exact ite_eq_right (by omega)
lemma truncated_eval_band (d : ℕ) (a : Polynomial R) (ha : a.natDegree ≤ d)
    (s t : Fin N) (hne : matrixEval (truncatedShift N (ZMod 2)) a s t≠0) :
    t.val ≤ s.val+d := by
  by_contra h
  exact hne (truncated_eval_outside d a ha s t (by omega))
lemma mod_no_wrap_or_low (_hN : 0<N) (d b : ℕ) (hd : d<N) (hb : b ≤ d)
    (s t : Fin N) (hout : s.val+d<N ∨ d ≤ t.val) :
    ((s.val+b)%N=t.val)↔(s.val+b=t.val) := by
  by_cases hw : s.val+b<N
  · rw [Nat.mod_eq_of_lt hw]
  · have hs := s.isLt
    have ht := t.isLt
    have hmod : (s.val+b)%N=s.val+b-N := Nat.mod_eq_sub_mod (by omega) |>.trans (Nat.mod_eq_of_lt (by omega))
    rw [hmod]
    rcases hout with hout|hout <;> omega
lemma shift_evals_agree_outside (hN : 0<N) (d : ℕ) (hd : d<N)
    (a : Polynomial R) (ha : a.natDegree ≤ d) (s t : Fin N)
    (hout : s.val+d<N ∨ d ≤ t.val) :
    matrixEval (cyclicShift N (ZMod 2)) a s t=
      matrixEval (truncatedShift N (ZMod 2)) a s t := by
  conv_lhs => rw [a.as_sum_support,map_sum,Matrix.sum_apply]
  conv_rhs => rw [a.as_sum_support,map_sum,Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro b hb
  rw [cyclic_eval_monomial hN,truncated_eval_monomial]
  have hbd := (Polynomial.le_natDegree_of_mem_supp b hb).trans ha
  simp only [mod_no_wrap_or_low hN d b hd hbd s t hout]
lemma cyclic_difference_wrap (hN : 0<N) (d : ℕ) (hd : d<N)
    (a : Polynomial R) (ha : a.natDegree ≤ d) (s t : Fin N)
    (hne : (matrixEval (cyclicShift N (ZMod 2)) a-
      matrixEval (truncatedShift N (ZMod 2)) a) s t≠0) :
    N ≤ s.val+d ∧ t.val<d := by
  by_contra h
  have hout : s.val+d<N ∨ d ≤ t.val := by omega
  exact hne (sub_eq_zero.mpr (shift_evals_agree_outside hN d hd a ha s t hout))
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
lemma rootWord_append (l k : List (Root n×R)) : rootWord (l++k)=rootWord l*rootWord k := by
  simp [rootWord]
lemma rootWord_inverse (l : List (Root n×R)) :
    rootWord (l.reverse.map (fun pa=>(pa.1,-pa.2)))=(rootWord l)⁻¹ := by
  induction l with
  | nil => simp [rootWord]
  | cons pa l ih =>
    simp only [List.reverse_cons,List.map_append,rootWord_append,List.map_cons,List.map_nil,ih]
    simp [rootWord,Steinberg.x_neg,mul_inv_rev]
lemma exists_rootWord (g : Steinberg n R) : ∃l : List (Root n×R),rootWord l=g := by
  have hg : g∈Subgroup.closure (Set.range (fun pa : Root n×R=>Steinberg.x pa.1 pa.2)) := by
    rw [Steinberg.closure_range_x];exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem g hg => obtain ⟨pa,rfl⟩:=hg;exact ⟨[pa],by simp [rootWord]⟩
  | one => exact ⟨[],by simp [rootWord]⟩
  | mul g h hg hh ihg ihh =>
    obtain ⟨l,rfl⟩:=ihg
    obtain ⟨k,rfl⟩:=ihh
    exact ⟨l++k,rootWord_append l k⟩
  | inv g hg ih =>
    obtain ⟨l,rfl⟩:=ih
    exact ⟨l.reverse.map (fun pa=>(pa.1,-pa.2)),rootWord_inverse l⟩
variable [Algebra (ZMod 2) R]
lemma wrappedProduct_eq (l : List (Root n×Polynomial R)) :
    wrappedProduct (wrapFactors (N:=N) l)=matrixSteinbergEval (cyclicShift N (ZMod 2)) (rootWord l) := by
  induction l with
  | nil => simp [wrappedProduct,wrapFactors,rootWord]
  | cons pa l ih =>
    simp only [wrapFactors,List.map_cons,wrappedProduct,List.prod_cons] at ih ⊢
    rw [ih]
    simp only [rootWord,List.map_cons,List.prod_cons,map_mul,matrixSteinbergEval_x]
    congr 2
    abel
lemma truncatedProduct_eq (l : List (Root n×Polynomial R)) :
    truncatedProduct (wrapFactors (N:=N) l)=matrixSteinbergEval (truncatedShift N (ZMod 2)) (rootWord l) := by
  induction l with
  | nil => simp [truncatedProduct,wrapFactors,rootWord]
  | cons pa l ih =>
    simp only [wrapFactors,List.map_cons,truncatedProduct,List.prod_cons] at ih ⊢
    rw [ih]
    simp only [rootWord,List.map_cons,List.prod_cons,map_mul,matrixSteinbergEval_x]
lemma wrapFactors_bounded (hN : 0<N) (d : ℕ) (hd : d<N) (l : List (Root n×Polynomial R))
    (hl : ∀pa∈l,pa.2.natDegree ≤ d) : ∀x∈wrapFactors (N:=N) l,x.Bounded d := by
  rintro _ hx
  obtain ⟨pa,hpa,rfl⟩ := List.mem_map.mp hx
  exact ⟨truncated_eval_band d pa.2 (hl pa hpa),cyclic_difference_wrap hN d hd pa.2 (hl pa hpa)⟩

theorem wrap_removal (l : List (Root n×Polynomial R)) (_hm : 1 ≤ l.length)
    (d : ℕ) (hl : ∀pa∈l,pa.2.natDegree ≤ d)
    (hN : 2*(l.length+1)*max 1 d<N)
    (hu : Elementary.representation (rootWord l)=1) :
    matrixSteinbergEval (cyclicShift N (ZMod 2)) (rootWord l)=
      matrixSteinbergEval (truncatedShift N (ZMod 2)) (rootWord l) := by
  have hpos : 0<N := by omega
  have hd : max 1 d<N := by nlinarith [Nat.zero_le (l.length*max 1 d)]
  have hb : 2*(((wrapFactors (N:=N) l).length+1)*max 1 d) ≤ N := by
    simp only [wrapFactors,List.length_map]
    nlinarith
  have he := band_wrap_removal (max 1 d) (wrapFactors (N:=N) l)
    (wrapFactors_bounded hpos (max 1 d) hd l (fun pa hpa=>(hl pa hpa).trans (Nat.le_max_right _ _))) hb
  rw [wrappedProduct_eq,truncatedProduct_eq] at he
  exact he (matrixSteinbergEval_kernel _ _ hu) (matrixSteinbergEval_kernel _ _ hu)
end
end SourceBurnside.Kernel

namespace SourceBurnside.WordAlgebra.Table
noncomputable section
variable {α K : Type*} [CommRing K] (T : Table α) (hh : T.Homogeneous)

lemma gradedElement_matrix_one {n : ℕ} (u : Steinberg n (T.Algebra (K:=K)))
    (hu : Elementary.representation u=1) :
    Elementary.representation (T.gradedElement hh u)=1 := by
  exact Elementary.map_kernel (T.gradingRingHom hh) u hu
lemma gradedElement_one {n : ℕ} (u : Steinberg n (T.Algebra (K:=K))) :
    Steinberg.map T.evalOne.toRingHom (T.gradedElement hh u)=u := by
  have he : T.evalOne.toRingHom.comp (T.gradingRingHom hh)=RingHom.id (T.Algebra (K:=K)) := by
    apply RingHom.ext
    intro x
    exact DFunLike.congr_fun (T.evalOne_gradingHom hh) x
  rw [gradedElement,Steinberg.map_map,he,Steinberg.map_identity_apply]
lemma gradedElement_zero {n : ℕ} (hz : ∀w,T.zero w → w≠1)
    (u : Steinberg n (T.Algebra (K:=K))) :
    Steinberg.map T.evalZero.toRingHom (T.gradedElement hh u)=
      Steinberg.map (algebraMap K (T.Algebra (K:=K))) (Steinberg.map (T.augmentation hh hz).toRingHom u) := by
  have he : T.evalZero.toRingHom.comp (T.gradingRingHom hh)=
      (algebraMap K (T.Algebra (K:=K))).comp (T.augmentation hh hz).toRingHom := by
    apply RingHom.ext
    intro x
    exact DFunLike.congr_fun (T.evalZero_gradingHom hh hz) x
  rw [gradedElement,Steinberg.map_map,Steinberg.map_map,he]
end
end SourceBurnside.WordAlgebra.Table

namespace SourceBurnside.ConcreteSource
noncomputable section

lemma gradedElement_matrix_one {n : ℕ} (u : Steinberg n R) (hu : Elementary.representation u=1) :
    Elementary.representation (gradedElement u)=1 := by
  exact (machine.table height (by rfl)).gradedElement_matrix_one (machine.table_homogeneous (by rfl)) u hu
lemma gradedElement_one {n : ℕ} (u : Steinberg n R) :
    Steinberg.map evalOne.toRingHom (gradedElement u)=u :=
  (machine.table height (by rfl)).gradedElement_one (machine.table_homogeneous (by rfl)) u
lemma gradedElement_zero {n : ℕ} (u : Steinberg n R) :
    Steinberg.map evalZero.toRingHom (gradedElement u)=
      Steinberg.map (algebraMap (ZMod 2) R) (groundElement u) :=
  (machine.table height (by rfl)).gradedElement_zero (machine.table_homogeneous (by rfl))
    (machine.table_zero_nonempty (by rfl)) u
end
end SourceBurnside.ConcreteSource

namespace SourceBurnside.Kernel
noncomputable section
variable {n m : ℕ} {S R : Type*} [Ring S] [Ring R]

theorem stable_uniqueness (hn : 3 ≤ n) (f g : Steinberg n S →* Steinberg m R)
    (he : ∀u,Elementary.representation (f u)=Elementary.representation (g u)) :
    padSteinberg.comp f=padSteinberg.comp g := by
  let H := Steinberg (m+1) R
  let F : Steinberg n S →* H := padSteinberg.comp f
  let G : Steinberg n S →* H := padSteinberg.comp g
  have hz (u : Steinberg n S) : F u*(G u)⁻¹∈Subgroup.center H := by
    have hh : Elementary.representation (f u*(g u)⁻¹)=1 := by
      rw [map_mul,map_inv,he u,mul_inv_cancel]
    have hc := stabilized_kernel_central (f u*(g u)⁻¹) hh
    simpa only [F,G,H,MonoidHom.comp_apply,map_mul,map_inv] using hc
  let : CommGroup (Subgroup.center H) :=
    { (inferInstance : Group (Subgroup.center H)) with
      mul_comm := fun a b=>Subtype.ext (b.property.comm a).symm }
  let ratio : Steinberg n S →* Subgroup.center H :=
    { toFun := fun u=>⟨F u*(G u)⁻¹,hz u⟩
      map_one' := by apply Subtype.ext;simp
      map_mul' := by
        intro u v
        apply Subtype.ext
        change F (u*v)*(G (u*v))⁻¹=(F u*(G u)⁻¹)*(F v*(G v)⁻¹)
        rw [map_mul,map_mul,mul_inv_rev]
        have hc : (F v*(G v)⁻¹)*(G u)⁻¹=(G u)⁻¹*(F v*(G v)⁻¹) :=
          (Subgroup.mem_center_iff.mp (hz v) ((G u)⁻¹)).symm
        calc
          _ = F u*((F v*(G v)⁻¹)*(G u)⁻¹) := by group
          _ = F u*((G u)⁻¹*(F v*(G v)⁻¹)) := congrArg (fun x=>F u*x) hc
          _ = _ := by group }
  have hr := Steinberg.hom_to_commGroup_trivial hn ratio
  apply MonoidHom.ext
  intro u
  have hu := congrArg Subtype.val (DFunLike.congr_fun hr u)
  change F u*(G u)⁻¹=1 at hu
  exact mul_inv_eq_one.mp hu
end
end SourceBurnside.Kernel
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]

lemma scalar_units_conjugates (P : (Matrix (Fin N) (Fin N) R)ˣ)
    (u : (Matrix (Fin n) (Fin n) (Matrix (Fin N) (Fin N) R))ˣ) :
    (Units.map (scalarRingHom (N:=n)).toMonoidHom P)*u*
      (Units.map (scalarRingHom (N:=n)).toMonoidHom P)⁻¹=
      Units.map (coefficientConj P).mapMatrix.toMonoidHom u := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  change ((Matrix.diagonal (fun _ : Fin n=>P.val))*u.val*(Matrix.diagonal (fun _ : Fin n=>P.inv))) i j=
    P.val*(u.val i j)*P.inv
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
lemma big_conjugates_elementary (P : (Matrix (Fin N) (Fin N) R)ˣ)
    (p : Root n) (A : Matrix (Fin N) (Fin N) R) :
    bigBasisUnits P*Elementary.representation (blockRoot p A)*(bigBasisUnits P)⁻¹=
      Elementary.representation (blockRoot p (coefficientConj P A)) := by
  have hs := scalar_units_conjugates (n:=n) P (Elementary.e p A)
  have he := congrArg (Units.map (flattenRing (n:=n) (N:=N) (R:=R)).toMonoidHom) hs
  simpa only [map_mul,map_inv,Elementary.map_e,representation_blockRoot,bigBasisUnits] using he

theorem stable_basis_change (hn : 3 ≤ n) (P : (Matrix (Fin N) (Fin N) R)ˣ)
    (b : Steinberg (n*N) R) (hb : Elementary.representation b=bigBasisUnits P)
    (u : Steinberg n (Matrix (Fin N) (Fin N) R)) :
    padSteinberg (b*blockMap u*b⁻¹)=
      padSteinberg (blockMap (Steinberg.map (coefficientConj P) u)) := by
  let f : Steinberg n (Matrix (Fin N) (Fin N) R) →* Steinberg (n*N) R :=
    (MulAut.conj b).toMonoidHom.comp blockMap
  let g : Steinberg n (Matrix (Fin N) (Fin N) R) →* Steinberg (n*N) R :=
    blockMap.comp (Steinberg.map (coefficientConj P))
  have he : Elementary.representation.comp f=Elementary.representation.comp g := by
    apply Steinberg.hom_ext
    intro p A
    change Elementary.representation (b*blockMap (Steinberg.x p A)*b⁻¹)=
      Elementary.representation (blockMap (Steinberg.map (coefficientConj P) (Steinberg.x p A)))
    rw [Steinberg.map_x,blockMap_x,blockMap_x,map_mul,map_mul,map_inv,hb]
    exact big_conjugates_elementary P p A
  have hu := DFunLike.congr_fun (stable_uniqueness hn f g (fun u=>DFunLike.congr_fun he u)) u
  exact hu
end
end SourceBurnside.Kernel

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_MatrixUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]
lemma bigBasisUnits_entry {S : Type*} [Ring S] (P : (Matrix (Fin N) (Fin N) S)ˣ)
    (i j : Fin n) (s t : Fin N) :
    (bigBasisUnits P).val (blockIndex i s) (blockIndex j t)=if i=j then P.val s t else 0 := by
  change flattenRing (Matrix.diagonal (fun _ : Fin n=>P.val)) (blockIndex i s) (blockIndex j t)=_
  simp only [flattenRing,RingEquiv.trans_apply,Matrix.coe_reindexRingEquiv,Matrix.reindex_apply,
    Matrix.submatrix_apply,blockIndex,Equiv.symm_apply_apply,Matrix.compRingEquiv_apply,Matrix.comp_apply]
  by_cases hij : i=j <;> simp [Matrix.diagonal,hij]
lemma bigBasisUnits_map (P : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ) :
    Units.map (algebraMap (ZMod 2) R).mapMatrix.toMonoidHom (bigBasisUnits (n:=n) P)=
      bigBasisUnits (numericUnits (R:=R) P) := by
  apply Units.ext
  apply Matrix.ext
  intro u v
  obtain ⟨⟨i,s⟩,rfl⟩ := finProdFinEquiv.surjective u
  obtain ⟨⟨j,t⟩,rfl⟩ := finProdFinEquiv.surjective v
  change algebraMap (ZMod 2) R ((bigBasisUnits P).val (blockIndex i s) (blockIndex j t))=
    (bigBasisUnits (numericUnits (R:=R) P)).val (blockIndex i s) (blockIndex j t)
  rw [bigBasisUnits_entry,bigBasisUnits_entry]
  split_ifs <;> simp [numericUnits]
lemma numerical_big_lift (P : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ) :
    ∃b : Steinberg (n*N) R,Elementary.representation b=bigBasisUnits (numericUnits (R:=R) P) := by
  have hdet : (bigBasisUnits (n:=n) P).val.det≠0 :=
    (Matrix.isUnits_det_units (bigBasisUnits (n:=n) P)).ne_zero
  obtain ⟨b,hb⟩ := numerical_matrix_lift (bigBasisUnits (n:=n) P).val hdet
  refine ⟨Steinberg.map (algebraMap (ZMod 2) R) b,?_⟩
  have hb' : Elementary.representation b=bigBasisUnits P := Units.ext hb
  have he := DFunLike.congr_fun (Elementary.representation_map (n:=n*N) (algebraMap (ZMod 2) R)) b
  change Elementary.representation (Steinberg.map (algebraMap (ZMod 2) R) b)=_
  simpa only [MonoidHom.comp_apply,hb',bigBasisUnits_map] using he
lemma numeric_conj_scalar (P : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ) (a : R) :
    coefficientConj (numericUnits (R:=R) P) (Matrix.scalar (Fin N) a)=Matrix.scalar (Fin N) a := by
  change (numericUnits (R:=R) P).val*Matrix.scalar (Fin N) a*(numericUnits (R:=R) P).inv=_
  have hc := (numeric_scalar_commute (R:=R) P.val a).eq
  change Matrix.scalar (Fin N) a*(numericUnits (R:=R) P).val=(numericUnits (R:=R) P).val*Matrix.scalar (Fin N) a at hc
  rw [←hc,mul_assoc,Units.val_inv,mul_one]
lemma numeric_conj_matrix (P : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ)
    (T : Matrix (Fin N) (Fin N) (ZMod 2)) :
    coefficientConj (numericUnits (R:=R) P) (numericMatrix (R:=R) T)=numericMatrix (R:=R) (P.val*T*P.inv) := by
  change (algebraMap (ZMod 2) R).mapMatrix P.val*(algebraMap (ZMod 2) R).mapMatrix T*
    (algebraMap (ZMod 2) R).mapMatrix P.inv=(algebraMap (ZMod 2) R).mapMatrix (P.val*T*P.inv)
  simp only [map_mul]
lemma matrixEval_conjugacy (P : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ)
    (T : Matrix (Fin N) (Fin N) (ZMod 2)) :
    (coefficientConj (numericUnits (R:=R) P)).comp (matrixEvalRingHom T)=
      matrixEvalRingHom (R:=R) (P.val*T*P.inv) := by
  apply Polynomial.ringHom_ext
  · intro a
    change coefficientConj (numericUnits (R:=R) P) (Polynomial.eval₂ _ _ (Polynomial.C a))=
      Polynomial.eval₂ _ _ (Polynomial.C a)
    rw [Polynomial.eval₂_C,Polynomial.eval₂_C]
    exact numeric_conj_scalar P a
  · change coefficientConj (numericUnits (R:=R) P) (Polynomial.eval₂ _ _ Polynomial.X)=
      Polynomial.eval₂ _ _ Polynomial.X
    rw [Polynomial.eval₂_X,Polynomial.eval₂_X]
    exact numeric_conj_matrix P T

theorem stable_numerical_similarity (hn : 3 ≤ n)
    (P : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ) (T : Matrix (Fin N) (Fin N) (ZMod 2))
    (u : Steinberg n (Polynomial R)) (hu : Elementary.representation u=1) :
    padSteinberg (matrixSteinbergEval T u)=padSteinberg (matrixSteinbergEval (P.val*T*P.inv) u) := by
  obtain ⟨b,hb⟩ := numerical_big_lift (n:=n) (R:=R) P
  have he := stable_basis_change hn (numericUnits (R:=R) P) b hb (Steinberg.map (matrixEvalRingHom T) u)
  rw [Steinberg.map_map,matrixEval_conjugacy] at he
  have hz := stabilized_kernel_central (matrixSteinbergEval T u) (matrixSteinbergEval_kernel T u hu)
  have hc : Commute (padSteinberg b) (padSteinberg (matrixSteinbergEval T u)) :=
    Subgroup.mem_center_iff.mp hz _
  change padSteinberg (b*matrixSteinbergEval T u*b⁻¹)=padSteinberg (matrixSteinbergEval (P.val*T*P.inv) u) at he
  simpa only [map_mul,map_inv,CommutatorCalculus.conj_of_commute hc] using he
end
end SourceBurnside.Kernel
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {N : ℕ}
lemma pascal_lower : (pascalMatrix N).IsLowerTriangular := by
  intro s t hst
  change s.val<t.val at hst
  change ((s.val.choose t.val : ℕ) : ZMod 2)=0
  rw [Nat.choose_eq_zero_of_lt hst,Nat.cast_zero]
lemma pascal_det : (pascalMatrix N).det=1 := by
  rw [Matrix.det_of_isLowerTriangular _ pascal_lower]
  simp [pascalMatrix]
lemma matrix_mul_truncated {R : Type*} [Ring R] (A : Matrix (Fin N) (Fin N) R) (s t : Fin N) :
    (A*truncatedShift N R) s t=if h : t.val=0 then 0 else A s ⟨t.val-1,by have := t.isLt;omega⟩ := by
  rw [Matrix.mul_apply]
  by_cases ht : t.val=0
  · rw [dite_eq_left ht]
    apply Finset.sum_eq_zero
    intro k _
    have he : k.val+1≠t.val := by omega
    simp [truncatedShift,he]
  · rw [dite_eq_right ht]
    let k : Fin N := ⟨t.val-1,by have := t.isLt;omega⟩
    rw [Finset.sum_eq_single k]
    · have he : k.val+1=t.val := by dsimp [k];omega
      simp [truncatedShift,he,k]
    · intro u _ huk
      have he : u.val+1≠t.val := by
        intro he
        apply huk
        apply Fin.ext
        dsimp [k]
        omega
      simp [truncatedShift,he]
    · simp
lemma cyclic_mul_matrix {R : Type*} [Ring R] (hN : 0<N)
    (A : Matrix (Fin N) (Fin N) R) (s t : Fin N) :
    (cyclicShift N R*A) s t=A ⟨(s.val+1)%N,Nat.mod_lt _ hN⟩ t := by
  rw [Matrix.mul_apply]
  let k : Fin N := ⟨(s.val+1)%N,Nat.mod_lt _ hN⟩
  rw [Finset.sum_eq_single k]
  · simp [cyclicShift,k]
  · intro u _ huk
    have he : (s.val+1)%N≠u.val := by intro he;apply huk;apply Fin.ext;exact he.symm
    simp [cyclicShift,he]
  · simp
lemma pascal_times_unipotent (s t : Fin N) :
    (pascalMatrix N*(1+truncatedShift N (ZMod 2))) s t=((s.val+1).choose t.val : ZMod 2) := by
  rw [mul_add,mul_one,Matrix.add_apply,matrix_mul_truncated]
  by_cases ht : t.val=0
  · simp [ht,pascalMatrix]
  · rw [dite_eq_right ht]
    change (s.val.choose t.val : ZMod 2)+(s.val.choose (t.val-1) : ZMod 2)=_
    have hk : t.val=(t.val-1)+1 := by omega
    conv_rhs => rw [hk,Nat.choose_succ_succ',Nat.cast_add]
    rw [←hk,add_comm]
lemma power_two_choose (k j : ℕ) (hj : j<2^k) :
    ((2^k).choose j : ZMod 2)=((0 : ℕ).choose j : ZMod 2) := by
  by_cases hz : j=0
  · simp [hz]
  · have hd : 2 ∣ (2^k).choose j := Nat.prime_two.dvd_choose_pow hz (by omega)
    have hc : ((2^k).choose j : ZMod 2)=0 := (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mpr hd
    rw [hc]
    have hj0 : 0<j := by omega
    rw [Nat.choose_eq_zero_of_lt hj0,Nat.cast_zero]
lemma cyclic_pascal (k : ℕ) :
    cyclicShift (2^k) (ZMod 2)*pascalMatrix (2^k)=
      pascalMatrix (2^k)*(1+truncatedShift (2^k) (ZMod 2)) := by
  ext s t
  rw [cyclic_mul_matrix (by positivity),pascal_times_unipotent]
  change (((s.val+1)%(2^k)).choose t.val : ZMod 2)=((s.val+1).choose t.val : ZMod 2)
  by_cases hs : s.val+1<2^k
  · rw [Nat.mod_eq_of_lt hs]
  · have he : s.val+1=2^k := by have := s.isLt;omega
    rw [he,Nat.mod_self]
    exact (power_two_choose k t.val t.isLt).symm

theorem cyclic_triangularization (k : ℕ) :
    ∃P : (Matrix (Fin (2^k)) (Fin (2^k)) (ZMod 2))ˣ,
      P.inv*cyclicShift (2^k) (ZMod 2)*P.val=1+truncatedShift (2^k) (ZMod 2) := by
  have hi : IsUnit (pascalMatrix (2^k)) := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [pascal_det];exact isUnit_one)
  obtain ⟨P,hP⟩ := hi
  refine ⟨P,?_⟩
  have he := cyclic_pascal k
  rw [←hP] at he
  calc
    _ = P.inv*(cyclicShift (2^k) (ZMod 2)*P.val) := by simp [mul_assoc]
    _ = P.inv*(P.val*(1+truncatedShift (2^k) (ZMod 2))) := congrArg (fun A=>P.inv*A) he
    _ = _ := by simp [←mul_assoc]
end
end SourceBurnside.Kernel
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]
lemma one_add_truncated_upper (N : ℕ) :
    ((1 : Matrix (Fin N) (Fin N) (ZMod 2))+truncatedShift N (ZMod 2)).IsUpperTriangular := by
  intro s t hts
  have hne : s≠t := ne_of_gt hts
  simp only [Matrix.add_apply,Matrix.one_apply,ite_eq_right hne,truncatedShift_upper hts,zero_add]
lemma one_add_truncated_diag (N : ℕ) (s : Fin N) :
    ((1 : Matrix (Fin N) (Fin N) (ZMod 2))+truncatedShift N (ZMod 2)) s s=1 := by
  simp [Matrix.add_apply,truncatedShift_diag]

theorem stable_cyclic_evaluation (hn : 3≤n) (k : ℕ)
    (u : Steinberg n (Polynomial R)) (hu : Elementary.representation u=1) :
    padSteinberg (matrixSteinbergEval (cyclicShift (2^k) (ZMod 2)) u)=
      padSteinberg (diagonalCopy (N:=2^k) (Steinberg.map (scalarEval 1) u)) := by
  obtain ⟨P,hP⟩ := cyclic_triangularization k
  have he := stable_numerical_similarity hn P⁻¹ (cyclicShift (2^k) (ZMod 2)) u hu
  change padSteinberg (matrixSteinbergEval (cyclicShift (2^k) (ZMod 2)) u)=
    padSteinberg (matrixSteinbergEval (P.inv*cyclicShift (2^k) (ZMod 2)*P.val) u) at he
  rw [hP,triangular_evaluation (one_add_truncated_upper _) 1 (one_add_truncated_diag _) u hu] at he
  exact he

theorem stable_diagonal_evaluations (hn : 3≤n) (l : List (Root n×Polynomial R))
    (hm : 1≤l.length) (d k : ℕ) (hl : ∀pa∈l,pa.2.natDegree≤d)
    (hN : 2*(l.length+1)*max 1 d<2^k)
    (hu : Elementary.representation (rootWord l)=1) :
    padSteinberg (diagonalCopy (N:=2^k) (Steinberg.map (scalarEval 1) (rootWord l)))=
      padSteinberg (diagonalCopy (N:=2^k) (Steinberg.map (scalarEval 0) (rootWord l))) := by
  rw [←stable_cyclic_evaluation hn k _ hu,wrap_removal l hm d hl hN hu]
  rw [triangular_evaluation truncatedShift_upper 0 truncatedShift_diag _ hu]
end
end SourceBurnside.Kernel
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
lemma copyUnitsHom_e (s : Fin N) (p : Root n) (a : R) :
    copyUnitsHom s (Elementary.e p a)=Elementary.e (blockPosition p (s,s)) a := by
  apply Units.ext
  apply Matrix.ext
  intro u v
  obtain ⟨⟨i,t⟩,rfl⟩ := finProdFinEquiv.surjective u
  obtain ⟨⟨j,z⟩,rfl⟩ := finProdFinEquiv.surjective v
  change (Matrix.blockDiagonal (Pi.mulSingle s (1+Matrix.single p.row p.col a))).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm (finProdFinEquiv (i,t)) (finProdFinEquiv (j,z))=
    (1+Matrix.single (blockIndex p.row s) (blockIndex p.col s) a) (finProdFinEquiv (i,t)) (finProdFinEquiv (j,z))
  simp only [Matrix.submatrix_apply,Equiv.symm_apply_apply,Matrix.blockDiagonal_apply,
    Pi.mulSingle_apply,Matrix.add_apply,Matrix.one_apply,Matrix.single_apply,blockIndex]
  by_cases htz : t=z <;> by_cases hts : t=s <;>
    simp_all [Matrix.add_apply,Matrix.one_apply,Matrix.single_apply,Prod.ext_iff,eq_comm,and_comm]
lemma copy_representation (s : Fin N) :
    Elementary.representation.comp (copyMap (n:=n) (R:=R) s)= (copyUnitsHom s).comp Elementary.representation := by
  apply Steinberg.hom_ext
  intro p a
  simp only [MonoidHom.comp_apply,copyMap_x,Elementary.representation_x,copyUnitsHom_e]
lemma copy_kernel (s : Fin N) (u : Steinberg n R) (hu : Elementary.representation u=1) :
    Elementary.representation (copyMap s u)=1 := by
  have he := DFunLike.congr_fun (copy_representation (n:=n) (R:=R) s) u
  simpa only [MonoidHom.comp_apply,hu,map_one] using he
variable [Algebra (ZMod 2) R]
lemma swap_coefficient_single (s t : Fin N) (a : R) :
    coefficientConj (numericUnits (R:=R) (swapUnits s t)) (Matrix.single s s a)=Matrix.single t t a := by
  change (Matrix.swap (ZMod 2) s t).map (algebraMap (ZMod 2) R)*Matrix.single s s a*
    (Matrix.swap (ZMod 2) s t).map (algebraMap (ZMod 2) R)=_
  rw [Matrix.map_swap,Matrix.swap,PEquiv.toMatrix_toPEquiv_mul,PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  have h (i : Fin N) : s=(Equiv.swap s t) i ↔ t=i := by
    constructor
    · intro h
      have he := congrArg (Equiv.swap s t) h
      simpa using he
    · intro he
      subst i
      simp
  simp only [Matrix.submatrix_apply,Equiv.symm_swap,Matrix.single_apply]
  simp only [id_eq,h]

theorem stable_copy_eq (hn : 3≤n) (s t : Fin N) (u : Steinberg n R)
    (hu : Elementary.representation u=1) : padSteinberg (copyMap s u)=padSteinberg (copyMap t u) := by
  obtain ⟨b,hb⟩ := numerical_big_lift (n:=n) (R:=R) (swapUnits s t)
  let f := (MulAut.conj b).toMonoidHom.comp (copyMap (n:=n) (R:=R) s)
  have he : Elementary.representation.comp f=Elementary.representation.comp (copyMap t) := by
    apply Steinberg.hom_ext
    intro p a
    change Elementary.representation (b*copyMap s (Steinberg.x p a)*b⁻¹)=
      Elementary.representation (copyMap t (Steinberg.x p a))
    rw [copyMap_x,copyMap_x,←blockRoot_single p s s a,←blockRoot_single p t t a,
      map_mul,map_mul,map_inv,hb,big_conjugates_elementary,swap_coefficient_single]
  have hf := DFunLike.congr_fun (stable_uniqueness hn f (copyMap t) (fun v=>DFunLike.congr_fun he v)) u
  have hz := stabilized_kernel_central (copyMap s u) (copy_kernel s u hu)
  have hc : Commute (padSteinberg b) (padSteinberg (copyMap s u)) := Subgroup.mem_center_iff.mp hz _
  change padSteinberg (b*copyMap s u*b⁻¹)=padSteinberg (copyMap t u) at hf
  simpa only [map_mul,map_inv,CommutatorCalculus.conj_of_commute hc] using hf
end
end SourceBurnside.Kernel
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R S : Type*} [Ring R] [Ring S]
lemma pad_ringMap (f : R →+* S) (u : Steinberg n R) :
    Steinberg.map f (padSteinberg u)=padSteinberg (Steinberg.map f u) := by
  have he : (Steinberg.map f).comp padSteinberg=padSteinberg.comp (Steinberg.map (n:=n) f) := by
    apply Steinberg.hom_ext
    intro p a
    simp [padSteinberg,Steinberg.map_x]
  exact DFunLike.congr_fun he u
lemma copy_ringMap (f : R →+* S) (s : Fin N) (u : Steinberg n R) :
    Steinberg.map f (copyMap s u)=copyMap s (Steinberg.map f u) := by
  have he : (Steinberg.map f).comp (copyMap s)=(copyMap s).comp (Steinberg.map (n:=n) f) := by
    apply Steinberg.hom_ext
    intro p a
    simp [Steinberg.map_x]
  exact DFunLike.congr_fun he u
lemma diagonalCopy_ringMap (f : R →+* S) (u : Steinberg n R) :
    Steinberg.map f (diagonalCopy (N:=N) u)=diagonalCopy (N:=N) (Steinberg.map f u) := by
  change Steinberg.map f (Finset.noncommProd Finset.univ (fun s : Fin N=>copyMap s u) (fun _ _ _ _ h=>copy_commute h u u))=
    Finset.noncommProd Finset.univ (fun s : Fin N=>copyMap s (Steinberg.map f u)) (fun _ _ _ _ h=>copy_commute h _ _)
  erw [Finset.map_noncommProd]
  apply Finset.noncommProd_congr rfl
  intro s _
  exact copy_ringMap f s u
variable [Algebra (ZMod 2) R]
lemma stable_diagonalCopy_pow (hn : 3≤n) (s : Fin N) (u : Steinberg n R)
    (hu : Elementary.representation u=1) :
    padSteinberg (diagonalCopy (N:=N) u)=padSteinberg (copyMap s u)^N := by
  change padSteinberg (Finset.noncommProd Finset.univ (fun t : Fin N=>copyMap t u) (fun _ _ _ _ h=>copy_commute h u u))=_
  erw [Finset.map_noncommProd]
  have he := Finset.noncommProd_eq_pow_card Finset.univ (fun t : Fin N=>padSteinberg (copyMap t u))
    (fun t ht z hz htz=>(copy_commute htz u u).map padSteinberg)
    (padSteinberg (copyMap s u)) (fun t _=>stable_copy_eq hn t s u hu)
  simpa using he

lemma stable_ground_diagonal_periodic (hn : 3≤n) (hN : 0<N) (v : Steinberg n (ZMod 2)) :
    ∃m : ℕ, 0 < m ∧
      (padSteinberg (diagonalCopy (N:=N) (Steinberg.map (algebraMap (ZMod 2) R) v)))^m=1 := by
  have hnN : 3≤n*N := by nlinarith
  obtain ⟨m,hm,he⟩ := stabilized_field_periodic hnN (diagonalCopy (N:=N) v)
  refine ⟨m,hm,?_⟩
  have hf := congrArg (Steinberg.map (algebraMap (ZMod 2) R)) he
  simpa only [map_pow,map_one,pad_ringMap,diagonalCopy_ringMap] using hf

theorem stable_word_copy_torsion (hn : 3≤n) (l : List (Root n×Polynomial R))
    (hm : 1≤l.length) (d k : ℕ) (hl : ∀pa∈l,pa.2.natDegree≤d)
    (hN : 2*(l.length+1)*max 1 d<2^k)
    (hu : Elementary.representation (rootWord l)=1)
    (v : Steinberg n (ZMod 2))
    (hv : Steinberg.map (scalarEval 0) (rootWord l)=Steinberg.map (algebraMap (ZMod 2) R) v)
    (s : Fin (2^k)) :
    ∃m : ℕ, 0 < m ∧
      (padSteinberg (copyMap s (Steinberg.map (scalarEval 1) (rootWord l))))^m=1 := by
  obtain ⟨a,ha,he⟩ := stable_ground_diagonal_periodic (R:=R) hn (show 0<2^k by positivity) v
  have hdiag := stable_diagonal_evaluations hn l hm d k hl hN hu
  rw [hv] at hdiag
  have hz := scalarEval_kernel 1 (rootWord l) hu
  rw [←hdiag,stable_diagonalCopy_pow hn s _ hz] at he
  refine ⟨2^k*a,Nat.mul_pos (by positivity) ha,?_⟩
  simpa only [pow_mul] using he
end
end SourceBurnside.Kernel
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]

theorem polynomial_kernel_copy_torsion (hn : 3≤n)
    (u : Steinberg n (Polynomial R)) (hu : Elementary.representation u=1)
    (v : Steinberg n (ZMod 2))
    (hv : Steinberg.map (scalarEval 0) u=Steinberg.map (algebraMap (ZMod 2) R) v) :
    ∃k : ℕ,∃s : Fin (2^k),∃m : ℕ, 0 < m ∧
      (padSteinberg (copyMap s (Steinberg.map (scalarEval 1) u)))^m=1 := by
  obtain ⟨l,hl⟩ := exists_rootWord u
  let p : Root n := ⟨⟨0,by omega⟩,⟨1,by omega⟩,by intro he;have hh : (0 : ℕ)=1 := congrArg Fin.val he;omega⟩
  let l' := l++[(p,(0 : Polynomial R))]
  have hl' : rootWord l'=u := by simp [l',rootWord,Steinberg.x_zero] at hl ⊢;exact hl
  have hm : 1≤l'.length := by dsimp [l'];simp
  let d := l'.toFinset.sup (fun pa=>pa.2.natDegree)
  have hd : ∀pa∈l',pa.2.natDegree≤d := by
    intro pa hpa
    exact Finset.le_sup (f:=fun pa : Root n×Polynomial R=>pa.2.natDegree) (List.mem_toFinset.mpr hpa)
  let k := 2*(l'.length+1)*max 1 d
  have hk : 2*(l'.length+1)*max 1 d<2^k := Nat.lt_two_pow_self
  let s : Fin (2^k) := ⟨0,by positivity⟩
  have hmat : Elementary.representation (rootWord l')=1 := hl' ▸ hu
  have hval : Steinberg.map (scalarEval 0) (rootWord l')=Steinberg.map (algebraMap (ZMod 2) R) v := hl' ▸ hv
  obtain ⟨m,hm,he⟩ := stable_word_copy_torsion hn l' hm d k hd hk hmat v hval s
  refine ⟨k,s,m,hm,?_⟩
  simpa only [hl'] using he
end
end SourceBurnside.Kernel
namespace SourceBurnside.WordAlgebra.Table
noncomputable section
open Classical
variable {α : Type*}
lemma scalarEval_zero (T : Table α) :
    Kernel.scalarEval (R:=T.Algebra (K:=ZMod 2)) 0=T.evalZero.toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [Kernel.scalarEval,evalZero]
  · simp [Kernel.scalarEval,evalZero]
lemma scalarEval_one (T : Table α) :
    Kernel.scalarEval (R:=T.Algebra (K:=ZMod 2)) 1=T.evalOne.toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [Kernel.scalarEval,evalOne]
  · simp [Kernel.scalarEval,evalOne]
end
end SourceBurnside.WordAlgebra.Table
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n m : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]
lemma permutation_conjugates_e (σ : Equiv.Perm (Fin m)) (p : Root m) (a : R) :
    numericUnits (R:=R) (permutationUnits σ)*Elementary.e p a*
      (numericUnits (R:=R) (permutationUnits σ))⁻¹=
      Elementary.e (p.map σ σ.injective) a := by
  apply Units.ext
  change (((σ⁻¹).permMatrix (ZMod 2)).map (algebraMap (ZMod 2) R))*(1+Matrix.single p.row p.col a)*
    ((σ.permMatrix (ZMod 2 )).map (algebraMap (ZMod 2) R))=1+Matrix.single (σ p.row) (σ p.col) a
  simp only [Equiv.Perm.permMatrix,PEquiv.map_toMatrix,PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv,Equiv.Perm.inv_def]
  ext i j
  simp [Matrix.submatrix_apply,Matrix.add_apply,Matrix.one_apply,Matrix.single_apply,
    ← Equiv.eq_symm_apply]

theorem stable_permutation_fixed (hm : 3 ≤ m) (σ : Equiv.Perm (Fin m))
    (u : Steinberg m R) (hu : Elementary.representation u=1) :
    padSteinberg (Steinberg.coordinateMap σ σ.injective u)=padSteinberg u := by
  obtain ⟨b,hb⟩ := numerical_lift (R:=R) (permutationUnits σ)
  let f := (MulAut.conj b).toMonoidHom
  let g := Steinberg.coordinateMap (R:=R) σ σ.injective
  have he : Elementary.representation.comp f=Elementary.representation.comp g := by
    apply Steinberg.hom_ext
    intro p a
    change Elementary.representation (b*Steinberg.x p a*b⁻¹)=_
    rw [map_mul,map_mul,map_inv,hb,Elementary.representation_x]
    change _=Elementary.representation (Steinberg.x (p.map σ σ.injective) a)
    rw [Elementary.representation_x]
    exact permutation_conjugates_e σ p a
  have hf := DFunLike.congr_fun (stable_uniqueness hm f g (fun v=>DFunLike.congr_fun he v)) u
  have hz := stabilized_kernel_central u hu
  have hc : Commute (padSteinberg b) (padSteinberg u) := Subgroup.mem_center_iff.mp hz _
  change padSteinberg (b*u*b⁻¹)=padSteinberg (Steinberg.coordinateMap σ σ.injective u) at hf
  simpa only [map_mul,map_inv,CommutatorCalculus.conj_of_commute hc] using hf.symm
omit [Algebra (ZMod 2) R] in
lemma coordinateMap_comp (f : Fin n→Fin m) (hf : Function.Injective f) {q : ℕ}
    (g : Fin m→Fin q) (hg : Function.Injective g) :
    (Steinberg.coordinateMap (R:=R) g hg).comp (Steinberg.coordinateMap f hf)=
      Steinberg.coordinateMap (g∘f) (hg.comp hf) := by
  apply Steinberg.hom_ext
  intro p a
  rfl

theorem stable_copy_to_standard (hn : 3 ≤ n) {N : ℕ} (hN : 0<N) (s : Fin N)
    (u : Steinberg n R) (hu : Elementary.representation u=1) :
    padSteinberg (copyMap s u)=
      padSteinberg (Steinberg.coordinateMap (Fin.castLE (show n≤n*N by nlinarith))
        (Fin.castLE_injective _) u) := by
  have hnm : n≤n*N := by nlinarith
  let f := fun i : Fin n=>blockIndex i s
  have hf : Function.Injective f := fun i j he=>congrArg Prod.fst (finProdFinEquiv.injective he)
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair f (Fin.castLE hnm) hf (Fin.castLE_injective _)
  have he := stable_permutation_fixed (R:=R) (by nlinarith : 3 ≤ n*N) σ (copyMap s u) (copy_kernel s u hu)
  have H : (Steinberg.coordinateMap (R:=R) σ σ.injective).comp (copyMap s)=
      Steinberg.coordinateMap (Fin.castLE hnm) (Fin.castLE_injective _) := by
    change (Steinberg.coordinateMap σ σ.injective).comp (Steinberg.coordinateMap f hf)=_
    rw [coordinateMap_comp]
    have heq : σ∘f=Fin.castLE hnm := funext hσ
    simp only [heq]
  have hU := DFunLike.congr_fun H u
  change Steinberg.coordinateMap σ σ.injective (copyMap s u)=
    Steinberg.coordinateMap (Fin.castLE hnm) (Fin.castLE_injective _) u at hU
  exact he.symm.trans (congrArg padSteinberg hU)
end
end SourceBurnside.Kernel
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]
omit [Algebra (ZMod 2) R] in
lemma pad_standard {q : ℕ} (hnq : n≤q) (u : Steinberg n R) :
    padSteinberg (Steinberg.coordinateMap (Fin.castLE hnq) (Fin.castLE_injective _) u)=
      Steinberg.coordinateMap (Fin.castLE (hnq.trans (Nat.le_succ q))) (Fin.castLE_injective _) u := by
  have H : padSteinberg.comp (Steinberg.coordinateMap (R:=R) (Fin.castLE hnq) (Fin.castLE_injective _))=
      Steinberg.coordinateMap (Fin.castLE (hnq.trans (Nat.le_succ q))) (Fin.castLE_injective _) := by
    apply Steinberg.hom_ext
    intro p a
    rfl
  exact DFunLike.congr_fun H u

theorem polynomial_kernel_standard_torsion (hn : 3≤n)
    (u : Steinberg n (Polynomial R)) (hu : Elementary.representation u=1)
    (v : Steinberg n (ZMod 2))
    (hv : Steinberg.map (scalarEval 0) u=Steinberg.map (algebraMap (ZMod 2) R) v) :
    ∃q : ℕ,∃hnq : n≤q,∃m : ℕ, 0 < m ∧
      (Steinberg.coordinateMap (Fin.castLE hnq) (Fin.castLE_injective _)
        (Steinberg.map (scalarEval 1) u))^m=1 := by
  obtain ⟨k,s,m,hm,he⟩ := polynomial_kernel_copy_torsion hn u hu v hv
  have hN : 0<2^k := by positivity
  have hnq : n≤n*2^k := by nlinarith
  have hcopy := stable_copy_to_standard hn hN s (Steinberg.map (scalarEval 1) u) (scalarEval_kernel 1 u hu)
  rw [hcopy,pad_standard] at he
  exact ⟨n*2^k+1,hnq.trans (Nat.le_succ _),m,hm,he⟩
end
end SourceBurnside.Kernel
namespace SourceBurnside.ConcreteSource
noncomputable section

theorem kernel_standard_stable_torsion {n : ℕ} (hn : 3≤n) (u : Steinberg n R)
    (hu : Elementary.representation u=1) :
    ∃q : ℕ,∃hnq : n≤q,∃m : ℕ, 0 < m ∧
      (Steinberg.coordinateMap (Fin.castLE hnq) (Fin.castLE_injective _) u)^m=1 := by
  have h0 : Kernel.scalarEval (R:=R) 0=evalZero.toRingHom :=
    (machine.table height (by rfl)).scalarEval_zero
  have h1 : Kernel.scalarEval (R:=R) 1=evalOne.toRingHom :=
    (machine.table height (by rfl)).scalarEval_one
  have hv : Steinberg.map (Kernel.scalarEval 0) (gradedElement u)=
      Steinberg.map (algebraMap (ZMod 2) R) (groundElement u) := by
    rw [h0]
    exact gradedElement_zero u
  obtain ⟨q,hnq,m,hm,he⟩ := Kernel.polynomial_kernel_standard_torsion hn (gradedElement u)
    (gradedElement_matrix_one u hu) (groundElement u) hv
  refine ⟨q,hnq,m,hm,?_⟩
  rw [h1,gradedElement_one] at he
  exact he
end
end SourceBurnside.ConcreteSource

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Homology_KernelStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SourceBurnside.Stability.RationalKernel

open Classical ElementaryRanks
variable {R : Type} [Ring R] [Algebra (ZMod 2) R]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

lemma kernelCast_refl (n : ℕ) : kernelCast ε (le_refl n)=MonoidHom.id _ := by
  apply MonoidHom.ext
  intro j
  apply Subtype.ext
  exact DFunLike.congr_fun (cast_refl (R := R) n) j.val
lemma kernelCast_succ {n q : ℕ} (hnq : n≤q) : kernelCast ε (hnq.trans (Nat.le_succ q))=
    (kernelStep ε q).comp (kernelCast ε hnq) := by
  apply MonoidHom.ext
  intro j
  apply Subtype.ext
  exact DFunLike.congr_fun (cast_succ (R := R) hnq) j.val

theorem restriction_cast_surjective (hI : MatrixNilKernel ε.toRingHom) {n q : ℕ}
    (hn : 12≤n) (hnq : n≤q) : Function.Surjective
    (fun ψ : J (R := R) q →* QGroup => ψ.comp (kernelCast ε hnq)) := by
  induction q,hnq using Nat.le_induction with
  | base =>
    intro φ
    refine ⟨φ,?_⟩
    dsimp only
    rw [kernelCast_refl,MonoidHom.comp_id]
  | succ q hnq ih =>
    intro φ
    obtain ⟨ψ,hψ⟩ := ih φ
    obtain ⟨χ,hχ⟩ := (restrictionIso ε hI q (hn.trans hnq)).surjective ψ
    change χ.comp (kernelStep ε q)=ψ at hχ
    refine ⟨χ,?_⟩
    dsimp only at hψ hχ ⊢
    rw [kernelCast_succ,←MonoidHom.comp_assoc,hχ]
    exact hψ

end SourceBurnside.Stability.RationalKernel

namespace SourceBurnside.Stability.RationalDetection
open Classical
variable {A : Type} [CommGroup A]

lemma character_nonzero_of_not_finite (a : A) (ha : ¬IsOfFinOrder a) :
    ∃φ : A →* QGroup, φ a=Multiplicative.ofAdd (1 : ℚ) := by
  let f : ℤ →ₗ[ℤ] Additive A := LinearMap.toSpanSingleton ℤ _ (Additive.ofMul a)
  have hf : Function.Injective f := by
    intro i j h
    apply (injective_zpow_iff_not_isOfFinOrder.mpr ha)
    exact congrArg Additive.toMul h
  let g : ℤ →ₗ[ℤ] ℚ := (Int.castAddHom ℚ).toIntLinearMap
  obtain ⟨h,hh⟩ := (Module.Baer.of_divisible ℚ).extension_property f hf g
  let φ : A →* QGroup :=
    { toFun := fun x => Multiplicative.ofAdd (h (Additive.ofMul x))
      map_one' := by change h 0=0; exact map_zero h
      map_mul' := fun x y => by
        change h (Additive.ofMul x+Additive.ofMul y)=h (Additive.ofMul x)+h (Additive.ofMul y)
        exact map_add h _ _ }
  refine ⟨φ,?_⟩
  have he := LinearMap.congr_fun hh 1
  change h (f 1)=g 1 at he
  have hg : g 1=1 := by simp [g]
  rw [hg] at he
  change h (Additive.ofMul a)=(1 : ℚ)
  simpa only [f,LinearMap.toSpanSingleton_apply,one_smul] using he

lemma finite_of_characters_vanish (a : A) (ha : ∀φ : A →* QGroup,φ a=1) : IsOfFinOrder a := by
  by_contra hn
  obtain ⟨φ,hφ⟩ := character_nonzero_of_not_finite a hn
  have he := ha φ
  rw [hφ] at he
  have : (1 : ℚ)=0 := congrArg Multiplicative.toAdd he
  exact one_ne_zero this

lemma character_finite_eq_one {B : Type} [Group B] (φ : B →* QGroup) {a : B} (ha : IsOfFinOrder a) : φ a=1 := by
  obtain ⟨m,hm,he⟩ := ha.exists_pow_eq_one
  have hφ : (φ a)^m=1 := by rw [←map_pow,he,map_one]
  have hx : (m : ℚ)*(φ a).toAdd=0 := by
    simpa only [toAdd_pow,toAdd_one,nsmul_eq_mul] using congrArg Multiplicative.toAdd hφ
  have hm' : (m : ℚ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  change (φ a).toAdd=0
  exact (mul_eq_zero.mp hx).resolve_left hm'

end SourceBurnside.Stability.RationalDetection

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Periodicity_KernelTorsion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SourceBurnside.ConcreteSource
noncomputable section
open Classical Stability Stability.RationalKernel
open scoped IsMulCommutative

theorem kernel_torsion_rank {n : ℕ} (hn : 12≤n) (u : Steinberg n R)
    (hu : Elementary.representation u=1) : ∃ m : ℕ, 0 < m ∧ u ^ m = 1 := by
  let j : J (R := R) n := ⟨u,Subtype.ext hu⟩
  let : IsMulCommutative (J (R := R) n) := ⟨⟨fun a b =>
    Subtype.ext ((central matrix_nil_kernel n (by omega) a.property).comm b.val).eq⟩⟩
  have hj : IsOfFinOrder j := by
    apply RationalDetection.finite_of_characters_vanish
    intro φ
    obtain ⟨q,hnq,m,hm,he⟩ := kernel_standard_stable_torsion (by omega) u hu
    obtain ⟨ψ,hψ⟩ := restriction_cast_surjective augmentation matrix_nil_kernel hn hnq φ
    have hfin : IsOfFinOrder (kernelCast augmentation hnq j) := by
      refine isOfFinOrder_iff_pow_eq_one.mpr ⟨m,hm,?_⟩
      exact Subtype.ext he
    have hz := RationalDetection.character_finite_eq_one ψ hfin
    have hx := DFunLike.congr_fun hψ j
    change ψ (kernelCast augmentation hnq j)=φ j at hx
    exact hx.symm.trans hz
  obtain ⟨m,hm,he⟩ := hj.exists_pow_eq_one
  exact ⟨m,hm,congrArg Subtype.val he⟩

theorem steinberg_periodic_rank {n : ℕ} (hn : 12≤n) : Periodic (Steinberg n R) := by
  intro g
  obtain ⟨a,ha,hea⟩ := matrix_periodic n (Elementary.representation g)
  have hker : Elementary.representation (g^a)=1 := by rw [map_pow,hea]
  obtain ⟨b,hb,heb⟩ := kernel_torsion_rank hn (g^a) hker
  exact ⟨a*b,Nat.mul_pos ha hb,by rw [pow_mul,heb]⟩

theorem steinberg_periodic : Periodic (Steinberg 12 R) := steinberg_periodic_rank (by decide)

theorem main : Infinite (Steinberg 12 R) ∧
    Group.IsFinitelyPresented (Steinberg 12 R) ∧ Periodic (Steinberg 12 R) :=
  ⟨steinberg_infinite,steinberg_finitely_presented,steinberg_periodic⟩

theorem main_statement : MainStatement := ⟨R,inferInstance,inferInstance,main⟩

theorem exists_infinite_finitely_presented_periodic_group :
    ∃ (G : Type) (hG : Group G), Infinite G ∧
      @Group.IsFinitelyPresented G hG ∧ @Periodic G hG :=
  ⟨Steinberg 12 R,inferInstance,main⟩

theorem burnside_statement : BurnsideStatement := exists_infinite_finitely_presented_periodic_group

end
end SourceBurnside.ConcreteSource

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SourceBurnside

theorem thm_main_oai : MainStatement ∧ BurnsideStatement :=
  ⟨ConcreteSource.main_statement, ConcreteSource.burnside_statement⟩

end SourceBurnside

end OAI
end

theorem solution : type_of% @OAI.SourceBurnside.thm_main_oai := @OAI.SourceBurnside.thm_main_oai
