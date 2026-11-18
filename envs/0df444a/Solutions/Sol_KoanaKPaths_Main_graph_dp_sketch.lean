-- Prove2me | solution 1 for KoanaKPaths.Main.graph_dp_sketch
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:46:16.371746+00:00
-- url     : https://prove2.me/submissions/f6575571-393c-484c-b2c5-a01a9c95f1c8

import Definitions.Def_KoanaKPaths_GraphDP
import Theorems.Thm_KoanaKPaths_Main_exterior_word_coordinates
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 4096
open scoped BigOperators Classical
namespace KoanaKPaths.ExteriorCoordinates
lemma det_enum_cast {k d e : ℕ} (S : Finset (Fin k)) (h : d = e)
    (hs : S.card = d) (f : ℕ → Fin k → ℤ) :
    Matrix.det (Matrix.of fun r c : Fin d => f c.val (S.orderEmbOfFin hs r)) =
    Matrix.det (Matrix.of fun r c : Fin e => f c.val (S.orderEmbOfFin (hs.trans h) r)) := by
  subst e
  rfl

lemma univ_enum {k : ℕ} (h : (Finset.univ : Finset (Fin k)).card = k) (r : Fin k) :
    (Finset.univ : Finset (Fin k)).orderEmbOfFin h r = r := by
  have he := Finset.orderEmbOfFin_unique h (f := id)
    (fun _ => Finset.mem_univ _) (strictMono_id)
  exact (congrFun he r).symm

theorem top_coordinate {k : ℕ} (vs : Fin k → Fin k → ℤ) :
    wordCoordinates (List.ofFn vs) Finset.univ =
      Matrix.det (Matrix.of fun r c : Fin k => vs c r) := by
  have hlen : (List.ofFn vs).length = k := List.length_ofFn
  have hs : (Finset.univ : Finset (Fin k)).card = (List.ofFn vs).length := by simp
  rw [(KoanaKPaths.Main.exterior_word_coordinates k (List.ofFn vs) Finset.univ).1,dif_pos hs]
  rw [det_enum_cast Finset.univ hlen hs (fun c => (List.ofFn vs).getD c (fun _ => 0))]
  congr 1
  funext r c
  simp only [Matrix.of_apply,univ_enum]
  simp [List.getD_eq_getElem?_getD,c.isLt]

lemma wedgeRight_zero {k : ℕ} (v : Fin k → ℤ) : wedgeRight (0 : Coordinates k) v = 0 := by
  funext S
  simp [wedgeRight]

lemma wedgeRight_add {k : ℕ} (A B : Coordinates k) (v : Fin k → ℤ) :
    wedgeRight (A+B) v = wedgeRight A v + wedgeRight B v := by
  funext S
  simp only [wedgeRight,Pi.add_apply]
  simp_rw [mul_add,add_mul]
  exact Finset.sum_add_distrib

lemma wedgeRight_smul {k : ℕ} (z : ℤ) (A : Coordinates k) (v : Fin k → ℤ) :
    wedgeRight (z • A) v = z • wedgeRight A v := by
  funext S
  simp only [wedgeRight,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

lemma wedgeRight_sum {k : ℕ} {α : Type} (s : Finset α) (A : α → Coordinates k)
    (v : Fin k → ℤ) :
    wedgeRight (∑ a ∈ s, A a) v = ∑ a ∈ s, wedgeRight (A a) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wedgeRight_zero]
  | @insert a s ha ih => simp only [Finset.sum_insert ha,wedgeRight_add,ih]


end KoanaKPaths.ExteriorCoordinates

set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 4096
open scoped BigOperators Classical
namespace KoanaKPaths.Main
open ExteriorCoordinates

lemma sum_snoc {α A : Type} [Fintype α] [AddCommMonoid A] (p : ℕ)
    (f : (Fin (p+1) → α) → A) :
    (∑ τ : Fin (p+1) → α, f τ) = ∑ j : α, ∑ τ : Fin p → α, f (Fin.snoc τ j) := by
  classical
  rw [← (Fin.snocEquiv (fun _ : Fin (p+1) => α)).sum_comp f,Fintype.sum_prod_type]
  rfl

lemma joinWord_zero {n k : ℕ} (τ : Fin 0 → Fin n) (ρ : Resid n k 0) :
    joinWord τ ρ = fullWord ρ := by
  funext r
  simp [joinWord,fullWord]

lemma joinWord_snoc {n k p : ℕ} (τ : Fin p → Fin n) (j : Fin n) (ρ : Resid n k (p+1)) :
    joinWord (Fin.snoc τ j) ρ = joinWord τ (extendResid ρ j) := by
  funext r
  by_cases hr : r.val < p
  · have hr1 : r.val < p+1 := by omega
    have he : (⟨r.val,hr1⟩ : Fin (p+1)) = (⟨r.val,hr⟩ : Fin p).castSucc := rfl
    simp only [joinWord,dif_pos hr1,dif_pos hr,he,Fin.snoc_castSucc]
  · by_cases he : r.val = p
    · have hr1 : r.val < p+1 := by omega
      have hj : (⟨r.val,hr1⟩ : Fin (p+1)) = Fin.last p := Fin.ext he
      simp only [joinWord,dif_pos hr1,dif_neg hr,hj,Fin.snoc_last,extendResid,dif_pos he]
    · have hr1 : ¬ r.val < p+1 := by omega
      simp only [joinWord,dif_neg hr1,dif_neg hr,extendResid,dif_neg he]

lemma joinWord_full {n k : ℕ} (τ : Fin k → Fin n) (ρ : Resid n k k) :
    joinWord τ ρ = τ := by
  funext r
  simp only [joinWord,dif_pos r.isLt]

lemma sketch_expansion {n k ℓ : ℕ} (c : (Fin k → Fin n) → ℤ)
    (σ : Labels n k) (R : SketchSigns n k ℓ) (i : ℕ) (hi : i < k)
    (a : Fin ℓ) (ρ : Resid n k (i+1)) :
    sketch c σ R i a ρ =
      ∑ τ : Fin (i+1) → Fin n, chainWeight R (i+1) τ a * Psi c σ (joinWord τ ρ) := by
  induction i generalizing a with
  | zero =>
    rw [sum_snoc]
    simp_rw [joinWord_snoc,joinWord_zero]
    simp [sketch,chainWeight,Fin.snoc_zero]
  | succ i ih =>
    have hi' : i < k-1 := by omega
    simp only [sketch,dif_pos hi']
    simp_rw [ih (by omega)]
    rw [sum_snoc]
    simp only [chainWeight,dif_pos hi',Fin.init_snoc,Fin.snoc_last]
    simp_rw [joinWord_snoc,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro τ _
    ring

private def Walk {n p : ℕ} (E : Finset (Fin n × Fin n)) (τ : Fin p → Fin n) : Prop :=
  ∀ (i : Fin p) (h : i.val+1 < p), (τ i,τ ⟨i.val+1,h⟩) ∈ E

private lemma walksTo_mem {n p : ℕ} (E : Finset (Fin n × Fin n))
    (τ : Fin (p+1) → Fin n) (v : Fin n) :
    τ ∈ PathCount2k.walksTo n E (p+1) v ↔ Walk E τ ∧ τ (Fin.last p) = v := by
  classical
  simp only [PathCount2k.walksTo,Finset.mem_filter,Finset.mem_univ,true_and]
  change Walk E τ ∧ (∀ h : 0 < p+1, τ (Fin.last p) = v) ↔ _
  simp

private lemma walk_one {n : ℕ} (E : Finset (Fin n × Fin n)) (τ : Fin 1 → Fin n) : Walk E τ := by
  intro i hi
  omega

private lemma walk_snoc {n p : ℕ} (E : Finset (Fin n × Fin n))
    (τ : Fin (p+1) → Fin n) (j : Fin n) :
    Walk E (Fin.snoc τ j) ↔ Walk E τ ∧ (τ (Fin.last p),j) ∈ E := by
  constructor
  · intro hw
    constructor
    · intro i hi
      have hh := hw i.castSucc (by simp only [Fin.val_castSucc]; omega)
      change ((Fin.snoc τ j : Fin (p+2) → Fin n) i.castSucc,
        (Fin.snoc τ j : Fin (p+2) → Fin n) (⟨i.val+1,hi⟩ : Fin (p+1)).castSucc) ∈ E at hh
      simpa only [Fin.snoc_castSucc] using hh
    · have hh := hw (Fin.last p).castSucc (by simp only [Fin.val_castSucc,Fin.val_last]; omega)
      change ((Fin.snoc τ j : Fin (p+2) → Fin n) (Fin.last p).castSucc,
        (Fin.snoc τ j : Fin (p+2) → Fin n) (Fin.last (p+1))) ∈ E at hh
      simpa only [Fin.snoc_castSucc,Fin.snoc_last] using hh
  · rintro ⟨hw,ha⟩ i hi
    have hp : i.val < p+1 := by omega
    have he : i = (⟨i.val,hp⟩ : Fin (p+1)).castSucc := Fin.ext rfl
    have hx : (Fin.snoc τ j : Fin (p+2) → Fin n) i = τ ⟨i.val,hp⟩ :=
      (congrArg (Fin.snoc τ j : Fin (p+2) → Fin n) he).trans (Fin.snoc_castSucc _ _ _)
    rw [hx]
    by_cases ht : i.val+1 < p+1
    · have hn : (⟨i.val+1,hi⟩ : Fin (p+2)) = (⟨i.val+1,ht⟩ : Fin (p+1)).castSucc := Fin.ext rfl
      rw [hn,Fin.snoc_castSucc]
      exact hw ⟨i.val,hp⟩ ht
    · have hv : i.val = p := by omega
      have hn : (⟨i.val+1,hi⟩ : Fin (p+2)) = Fin.last (p+1) := Fin.ext (by simp only [Fin.val_last]; omega)
      rw [hn,Fin.snoc_last]
      have hl : (⟨i.val,hp⟩ : Fin (p+1)) = Fin.last p := Fin.ext hv
      simpa only [hl] using ha

private lemma walksTo_one {n : ℕ} (E : Finset (Fin n × Fin n)) (v : Fin n) :
    PathCount2k.walksTo n E 1 v = {fun _ => v} := by
  classical
  ext τ
  rw [walksTo_mem,Finset.mem_singleton]
  constructor
  · intro ht
    funext i
    have hi : i = Fin.last 0 := Subsingleton.elim _ _
    simpa only [hi] using ht.2
  · intro he
    subst τ
    exact ⟨walk_one _ _,rfl⟩

private def labelWord {n k p : ℕ} (σ : Labels n k) (τ : Fin p → Fin n) : List (Fin k → ℤ) :=
  List.ofFn (fun i => fun r => sgn (σ (τ i) r))

private lemma labelWord_snoc {n k p : ℕ} (σ : Labels n k) (τ : Fin p → Fin n) (j : Fin n) :
    labelWord σ (Fin.snoc τ j) = labelWord σ τ ++ [fun r => sgn (σ j r)] := by
  unfold labelWord
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc,Fin.snoc_last,List.concat_eq_append]

private lemma wordCoordinates_append {k : ℕ} (vs : List (Fin k → ℤ)) (v : Fin k → ℤ) :
    wordCoordinates (vs++[v]) = wedgeRight (wordCoordinates vs) v := by
  simp only [wordCoordinates,List.foldl_append,List.foldl_cons,List.foldl_nil]

private lemma wedgeRight_ite {k : ℕ} (P : Prop) [Decidable P] (A : Coordinates k) (v : Fin k → ℤ) :
    wedgeRight (if P then A else 0) v = if P then wedgeRight A v else 0 := by
  by_cases h : P <;> simp [h,wedgeRight_zero]

private lemma endpoint_sum {n p : ℕ} {A : Type} [AddCommMonoid A]
    (E : Finset (Fin n × Fin n)) (τ : Fin (p+1) → Fin n) (v : Fin n) (z : A) :
    (∑ u : Fin n, if (u,v) ∈ E then
      if τ ∈ PathCount2k.walksTo n E (p+1) u then z else 0 else 0) =
      if Walk E τ ∧ (τ (Fin.last p),v) ∈ E then z else 0 := by
  classical
  rw [Finset.sum_eq_single (τ (Fin.last p))]
  · by_cases hw : Walk E τ <;> by_cases ha : (τ (Fin.last p),v) ∈ E <;> simp [walksTo_mem,hw,ha]
  · intro u _ hu
    simp [walksTo_mem,Ne.symm hu]
  · simp

private lemma sum_last_eq {I A : Type} [Fintype I] [DecidableEq I] [AddCommMonoid A]
    (P : I → Prop) [DecidablePred P] (f : I → A) (v : I) :
    (∑ j, if P j ∧ j=v then f j else 0) = if P v then f v else 0 := by
  classical
  rw [Finset.sum_eq_single v]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

private lemma ite_fintype_sum {I A : Type} [Fintype I] [AddCommMonoid A]
    (P : Prop) [Decidable P] (f : I → A) :
    (if P then ∑ i, f i else 0) = ∑ i, if P then f i else 0 := by
  by_cases h : P <;> simp [h]

private lemma sum_triple_rotate {I J K A : Type} [Fintype I] [Fintype J] [Fintype K]
    [AddCommMonoid A] (f : I → J → K → A) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ j, ∑ i, f i j k := by
  calc
    _ = ∑ j, ∑ i, ∑ k, f i j k := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, f i j k := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

private lemma graphLayer_expansion {n k ℓ : ℕ} (arcs : List (Fin n × Fin n))
    (σ : Labels n k) (R : SketchSigns n k ℓ) (p : ℕ) (hp : p < k)
    (v : Fin n) (a : Fin ℓ) :
    graphLayer arcs σ R (p+1) v a =
      ∑ τ : Fin (p+1) → Fin n, if τ ∈ PathCount2k.walksTo n arcs.toFinset (p+1) v then
        chainWeight R (p+1) τ a • wordCoordinates (labelWord σ τ) else 0 := by
  classical
  induction p generalizing v a with
  | zero =>
    simp [graphLayer,walksTo_one,chainWeight,labelWord,List.ofFn_succ,Fin.snoc_zero]
  | succ p ih =>
    have hp' : p < k-1 := by omega
    simp only [graphLayer,dif_pos hp']
    simp only [ih (by omega),Finset.smul_sum,smul_ite,smul_zero,smul_smul]
    simp only [wedgeRight_sum,wedgeRight_ite,wedgeRight_smul,← wordCoordinates_append]
    rw [sum_snoc]
    simp only [walksTo_mem,walk_snoc,Fin.snoc_last,chainWeight,dif_pos hp',Fin.init_snoc,labelWord_snoc]
    simp_rw [Finset.sum_smul]
    conv_rhs => rw [Finset.sum_comm]
    simp_rw [sum_last_eq,ite_fintype_sum]
    rw [sum_triple_rotate]
    simp_rw [← walksTo_mem,endpoint_sum]

private lemma sum_walksTo {n p : ℕ} {A : Type} [AddCommMonoid A]
    (E : Finset (Fin n × Fin n)) (τ : Fin (p+1) → Fin n) (z : A) :
    (∑ v : Fin n, if τ ∈ PathCount2k.walksTo n E (p+1) v then z else 0) =
      if Walk E τ then z else 0 := by
  classical
  rw [Finset.sum_eq_single (τ (Fin.last p))]
  · simp [walksTo_mem]
  · intro v _ hv
    simp [walksTo_mem,Ne.symm hv]
  · simp

private lemma graphOutput_coefficient {n p ℓ : ℕ} (arcs : List (Fin n × Fin n))
    (σ : Labels n (p+1)) (R : SketchSigns n (p+1) ℓ) (a : Fin ℓ)
    (ρ : Resid n (p+1) (p+1)) :
    graphOutput arcs σ R a Finset.univ = sketch (walkTensor n arcs (p+1)) σ R p a ρ := by
  have hex (v : Fin n) := graphLayer_expansion arcs σ R p (by omega) v a
  have htop (τ : Fin (p+1) → Fin n) :
      wordCoordinates (labelWord σ τ) Finset.univ = detD σ τ := by
    exact top_coordinate (fun i r => sgn (σ (τ i) r))
  unfold graphOutput
  simp only [Finset.sum_apply]
  simp only [hex,Finset.sum_apply,ite_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,htop]
  rw [Finset.sum_comm]
  rw [sketch_expansion _ _ _ p (by omega)]
  simp only [joinWord_full,sum_walksTo]
  apply Finset.sum_congr rfl
  intro τ _
  have hc : walkTensor n arcs (p+1) τ = if Walk arcs.toFinset τ then 1 else 0 := by
    unfold walkTensor Walk
    split_ifs <;> rfl
  simp only [Psi,hc]
  by_cases hw : Walk arcs.toFinset τ <;> simp [hw]


theorem graph_dp_sketch {n k ℓ : ℕ} (hk : 1 ≤ k) (arcs : List (Fin n × Fin n))
    (σ : Labels n k) (R : SketchSigns n k ℓ) :
    (∑ a : Fin ℓ, (graphOutput arcs σ R a Finset.univ)^2) =
      sketchFrobSq (walkTensor n arcs k) σ R k := by
  cases k with
  | zero => omega
  | succ p =>
    simp only [sketchFrobSq]
    apply Finset.sum_congr rfl
    intro a _
    have he (ρ : Resid n (p+1) (p+1)) := graphOutput_coefficient arcs σ R a ρ
    simp_rw [← he]
    have hres : Fintype.card (Resid n (p+1) (p+1)) = 1 := by
      haveI : IsEmpty {r : Fin (p+1) // p+1 ≤ r.val} := ⟨fun r => by have := r.1.isLt; omega⟩
      haveI : Unique (Resid n (p+1) (p+1)) := by unfold Resid; infer_instance
      exact Fintype.card_unique
    simp only [Finset.sum_const,Finset.card_univ,hres,one_nsmul]

end KoanaKPaths.Main

theorem solution {n k ℓ : ℕ} (hk : 1 ≤ k) (arcs : List (Fin n × Fin n))
    (σ : KoanaKPaths.Main.Labels n k) (R : KoanaKPaths.Main.SketchSigns n k ℓ) :
    (∑ a : Fin ℓ, (KoanaKPaths.Main.graphOutput arcs σ R a Finset.univ)^2) =
      KoanaKPaths.Main.sketchFrobSq (KoanaKPaths.Main.walkTensor n arcs k) σ R k := by
  exact KoanaKPaths.Main.graph_dp_sketch hk arcs σ R
