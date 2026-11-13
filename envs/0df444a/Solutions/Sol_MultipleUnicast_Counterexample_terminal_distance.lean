-- Prove2me | solution 1 for MultipleUnicast.Counterexample.terminal_distance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:37:10.283568+00:00
-- url     : https://prove2.me/submissions/177212d2-624e-46d1-a8cd-d127b1d68ade

import Mathlib
import Definitions.Def_MultipleUnicast_Counterexample_Graph
import Definitions.Def_MultipleUnicast_Counterexample_Protocol
import Theorems.Thm_MultipleUnicast_Counterexample_balanced_orientation

section
set_option maxRecDepth 4096
set_option autoImplicit false
set_option Elab.async false

/-! The incidence rows of PG(2,9), checked in ten small kernel computations. -/

namespace MultipleUnicast.Counterexample.Dev.IncRows
open MultipleUnicast.Counterexample

def rowT : List (List ℕ) := [[1, 10, 19, 28, 37, 46, 55, 64, 73, 82], [0, 10, 11, 12, 13, 14, 15, 16, 17, 18], [3, 10, 21, 29, 43, 54, 62, 67, 78, 86], [2, 10, 20, 30, 40, 50, 60, 70, 80, 90], [4, 10, 22, 34, 39, 51, 63, 65, 77, 89], [8, 10, 26, 33, 41, 48, 61, 72, 76, 83], [9, 10, 27, 32, 44, 49, 57, 69, 74, 88], [7, 10, 25, 31, 38, 53, 59, 66, 81, 87], [5, 10, 23, 36, 42, 52, 56, 71, 75, 85], [6, 10, 24, 35, 45, 47, 58, 68, 79, 84], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [1, 12, 21, 30, 39, 48, 57, 66, 75, 84], [1, 11, 20, 29, 38, 47, 56, 65, 74, 83], [1, 13, 22, 31, 40, 49, 58, 67, 76, 85], [1, 17, 26, 35, 44, 53, 62, 71, 80, 89], [1, 18, 27, 36, 45, 54, 63, 72, 81, 90], [1, 16, 25, 34, 43, 52, 61, 70, 79, 88], [1, 14, 23, 32, 41, 50, 59, 68, 77, 86], [1, 15, 24, 33, 42, 51, 60, 69, 78, 87], [0, 28, 29, 30, 31, 32, 33, 34, 35, 36], [3, 12, 20, 28, 45, 53, 61, 69, 77, 85], [2, 11, 21, 28, 41, 51, 58, 71, 81, 88], [4, 13, 25, 28, 42, 54, 57, 68, 80, 83], [8, 17, 24, 28, 39, 52, 59, 67, 74, 90], [9, 18, 23, 28, 40, 48, 62, 65, 79, 87], [7, 16, 22, 28, 44, 50, 56, 72, 78, 84], [5, 14, 27, 28, 43, 47, 60, 66, 76, 89], [6, 15, 26, 28, 38, 49, 63, 70, 75, 86], [0, 19, 20, 21, 22, 23, 24, 25, 26, 27], [2, 12, 19, 29, 42, 49, 59, 72, 79, 89], [3, 11, 19, 30, 44, 52, 63, 68, 76, 87], [7, 13, 19, 34, 41, 47, 62, 69, 75, 90], [6, 17, 19, 33, 40, 54, 56, 66, 77, 88], [5, 18, 19, 32, 38, 51, 61, 67, 80, 84], [4, 16, 19, 31, 45, 48, 60, 71, 74, 86], [9, 14, 19, 36, 39, 53, 58, 70, 78, 83], [8, 15, 19, 35, 43, 50, 57, 65, 81, 85], [0, 37, 38, 39, 40, 41, 42, 43, 44, 45], [7, 12, 27, 33, 37, 52, 58, 65, 80, 86], [4, 11, 23, 35, 37, 49, 61, 66, 78, 90], [3, 13, 24, 32, 37, 48, 56, 70, 81, 89], [5, 17, 21, 31, 37, 50, 63, 69, 79, 83], [8, 18, 22, 29, 37, 53, 60, 68, 75, 88], [2, 16, 26, 36, 37, 47, 57, 67, 77, 87], [6, 14, 25, 30, 37, 51, 62, 72, 74, 85], [9, 15, 20, 34, 37, 54, 59, 71, 76, 84], [0, 73, 74, 75, 76, 77, 78, 79, 80, 81], [9, 12, 26, 31, 43, 51, 56, 68, 73, 90], [5, 11, 24, 34, 40, 53, 57, 72, 73, 86], [6, 13, 27, 29, 39, 50, 61, 71, 73, 87], [3, 17, 25, 36, 41, 49, 60, 65, 73, 84], [4, 18, 21, 33, 44, 47, 59, 70, 73, 85], [8, 16, 23, 30, 38, 54, 58, 69, 73, 89], [7, 14, 20, 35, 42, 48, 63, 67, 73, 88], [2, 15, 22, 32, 45, 52, 62, 66, 73, 83], [0, 82, 83, 84, 85, 86, 87, 88, 89, 90], [8, 12, 25, 32, 40, 47, 63, 71, 78, 82], [6, 11, 22, 36, 43, 48, 59, 69, 80, 82], [9, 13, 21, 35, 38, 52, 60, 72, 77, 82], [7, 17, 23, 29, 45, 51, 57, 70, 76, 82], [3, 18, 26, 34, 42, 50, 58, 66, 74, 82], [5, 16, 20, 33, 39, 49, 62, 68, 81, 82], [2, 14, 24, 31, 44, 54, 61, 65, 75, 82], [4, 15, 27, 30, 41, 53, 56, 67, 79, 82], [0, 64, 65, 66, 67, 68, 69, 70, 71, 72], [4, 12, 24, 36, 38, 50, 62, 64, 76, 88], [7, 11, 26, 32, 39, 54, 60, 64, 79, 85], [2, 13, 23, 33, 43, 53, 63, 64, 74, 84], [9, 17, 22, 30, 42, 47, 61, 64, 81, 86], [6, 18, 20, 31, 41, 52, 57, 64, 78, 89], [3, 16, 27, 35, 40, 51, 59, 64, 75, 83], [8, 14, 21, 34, 45, 49, 56, 64, 80, 87], [5, 15, 25, 29, 44, 48, 58, 64, 77, 90], [0, 46, 47, 48, 49, 50, 51, 52, 53, 54], [6, 12, 23, 34, 44, 46, 60, 67, 81, 83], [8, 11, 27, 31, 42, 46, 62, 70, 77, 84], [5, 13, 26, 30, 45, 46, 59, 65, 78, 88], [4, 17, 20, 32, 43, 46, 58, 72, 75, 87], [2, 18, 25, 35, 39, 46, 56, 69, 76, 86], [9, 16, 24, 29, 41, 46, 63, 66, 80, 85], [3, 14, 22, 33, 38, 46, 57, 71, 79, 90], [7, 15, 21, 36, 40, 46, 61, 68, 74, 89], [0, 55, 56, 57, 58, 59, 60, 61, 62, 63], [5, 12, 22, 35, 41, 54, 55, 70, 74, 87], [9, 11, 25, 33, 45, 50, 55, 67, 75, 89], [8, 13, 20, 36, 44, 51, 55, 66, 79, 86], [2, 17, 27, 34, 38, 48, 55, 68, 78, 85], [7, 18, 24, 30, 43, 49, 55, 71, 77, 83], [6, 16, 21, 32, 42, 53, 55, 65, 76, 90], [4, 14, 26, 29, 40, 52, 55, 69, 81, 84], [3, 15, 23, 31, 39, 47, 55, 72, 80, 88]]

def row (i : Fin 91) : List ℕ :=
  ((List.finRange 91).filter fun j => dot (triple i) (triple j) = 0).map Fin.val

theorem row_chunk0 : ∀ i : Fin 91, 0 ≤ i.val → i.val < 10 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_chunk1 : ∀ i : Fin 91, 10 ≤ i.val → i.val < 20 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_chunk2 : ∀ i : Fin 91, 20 ≤ i.val → i.val < 30 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_chunk3 : ∀ i : Fin 91, 30 ≤ i.val → i.val < 40 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_chunk4 : ∀ i : Fin 91, 40 ≤ i.val → i.val < 50 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_chunk5 : ∀ i : Fin 91, 50 ≤ i.val → i.val < 60 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_chunk6 : ∀ i : Fin 91, 60 ≤ i.val → i.val < 70 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_chunk7 : ∀ i : Fin 91, 70 ≤ i.val → i.val < 80 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_chunk8 : ∀ i : Fin 91, 80 ≤ i.val → i.val < 90 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_chunk9 : ∀ i : Fin 91, 90 ≤ i.val → i.val < 100 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_eq (i : Fin 91) : row i = rowT.getD i.val [] := by
  have h := i.isLt
  by_cases h0 : i.val < 10; · exact row_chunk0 i (by omega) h0
  by_cases h1 : i.val < 20; · exact row_chunk1 i (by omega) h1
  by_cases h2 : i.val < 30; · exact row_chunk2 i (by omega) h2
  by_cases h3 : i.val < 40; · exact row_chunk3 i (by omega) h3
  by_cases h4 : i.val < 50; · exact row_chunk4 i (by omega) h4
  by_cases h5 : i.val < 60; · exact row_chunk5 i (by omega) h5
  by_cases h6 : i.val < 70; · exact row_chunk6 i (by omega) h6
  by_cases h7 : i.val < 80; · exact row_chunk7 i (by omega) h7
  by_cases h8 : i.val < 90; · exact row_chunk8 i (by omega) h8
  exact row_chunk9 i (by omega) (by omega)

theorem incidenceList_map :
    incidenceList.map (fun p => (p.1.val, p.2.val)) =
      (List.finRange 91).flatMap (fun i => (rowT.getD i.val []).map (fun j => (i.val, j))) := by
  unfold incidenceList
  rw [List.map_flatMap]
  congr 1
  funext i
  rw [← row_eq, row, List.map_map, List.map_map]
  rfl

end MultipleUnicast.Counterexample.Dev.IncRows
end

section
set_option maxRecDepth 4096
set_option autoImplicit false
set_option Elab.async false
namespace MultipleUnicast.Counterexample.Dev.Bal
open MultipleUnicast.Counterexample

def incTabs : List (List (ℕ × ℕ)) := [[(0,1),(0,10),(0,19),(0,28),(0,37),(0,46),(0,55),(0,64),(0,73),(0,82),(1,0),(1,10),(1,11),(1,12),(1,13),(1,14),(1,15),(1,16),(1,17),(1,18),(2,3),(2,10),(2,21),(2,29),(2,43),(2,54),(2,62),(2,67),(2,78),(2,86),(3,2),(3,10),(3,20),(3,30),(3,40),(3,50),(3,60),(3,70),(3,80),(3,90),(4,4),(4,10),(4,22),(4,34),(4,39),(4,51),(4,63),(4,65),(4,77),(4,89),(5,8),(5,10),(5,26),(5,33),(5,41),(5,48),(5,61),(5,72),(5,76),(5,83),(6,9),(6,10),(6,27),(6,32),(6,44),(6,49),(6,57),(6,69),(6,74),(6,88),(7,7),(7,10),(7,25),(7,31),(7,38),(7,53),(7,59),(7,66),(7,81),(7,87),(8,5),(8,10),(8,23),(8,36),(8,42),(8,52),(8,56),(8,71),(8,75),(8,85),(9,6)],
  [(9,10),(9,24),(9,35),(9,45),(9,47),(9,58),(9,68),(9,79),(9,84),(10,0),(10,1),(10,2),(10,3),(10,4),(10,5),(10,6),(10,7),(10,8),(10,9),(11,1),(11,12),(11,21),(11,30),(11,39),(11,48),(11,57),(11,66),(11,75),(11,84),(12,1),(12,11),(12,20),(12,29),(12,38),(12,47),(12,56),(12,65),(12,74),(12,83),(13,1),(13,13),(13,22),(13,31),(13,40),(13,49),(13,58),(13,67),(13,76),(13,85),(14,1),(14,17),(14,26),(14,35),(14,44),(14,53),(14,62),(14,71),(14,80),(14,89),(15,1),(15,18),(15,27),(15,36),(15,45),(15,54),(15,63),(15,72),(15,81),(15,90),(16,1),(16,16),(16,25),(16,34),(16,43),(16,52),(16,61),(16,70),(16,79),(16,88),(17,1),(17,14),(17,23),(17,32),(17,41),(17,50),(17,59),(17,68),(17,77),(17,86),(18,1),(18,15)],
  [(18,24),(18,33),(18,42),(18,51),(18,60),(18,69),(18,78),(18,87),(19,0),(19,28),(19,29),(19,30),(19,31),(19,32),(19,33),(19,34),(19,35),(19,36),(20,3),(20,12),(20,20),(20,28),(20,45),(20,53),(20,61),(20,69),(20,77),(20,85),(21,2),(21,11),(21,21),(21,28),(21,41),(21,51),(21,58),(21,71),(21,81),(21,88),(22,4),(22,13),(22,25),(22,28),(22,42),(22,54),(22,57),(22,68),(22,80),(22,83),(23,8),(23,17),(23,24),(23,28),(23,39),(23,52),(23,59),(23,67),(23,74),(23,90),(24,9),(24,18),(24,23),(24,28),(24,40),(24,48),(24,62),(24,65),(24,79),(24,87),(25,7),(25,16),(25,22),(25,28),(25,44),(25,50),(25,56),(25,72),(25,78),(25,84),(26,5),(26,14),(26,27),(26,28),(26,43),(26,47),(26,60),(26,66),(26,76),(26,89),(27,6),(27,15),(27,26)],
  [(27,28),(27,38),(27,49),(27,63),(27,70),(27,75),(27,86),(28,0),(28,19),(28,20),(28,21),(28,22),(28,23),(28,24),(28,25),(28,26),(28,27),(29,2),(29,12),(29,19),(29,29),(29,42),(29,49),(29,59),(29,72),(29,79),(29,89),(30,3),(30,11),(30,19),(30,30),(30,44),(30,52),(30,63),(30,68),(30,76),(30,87),(31,7),(31,13),(31,19),(31,34),(31,41),(31,47),(31,62),(31,69),(31,75),(31,90),(32,6),(32,17),(32,19),(32,33),(32,40),(32,54),(32,56),(32,66),(32,77),(32,88),(33,5),(33,18),(33,19),(33,32),(33,38),(33,51),(33,61),(33,67),(33,80),(33,84),(34,4),(34,16),(34,19),(34,31),(34,45),(34,48),(34,60),(34,71),(34,74),(34,86),(35,9),(35,14),(35,19),(35,36),(35,39),(35,53),(35,58),(35,70),(35,78),(35,83),(36,8),(36,15),(36,19),(36,35)],
  [(36,43),(36,50),(36,57),(36,65),(36,81),(36,85),(37,0),(37,37),(37,38),(37,39),(37,40),(37,41),(37,42),(37,43),(37,44),(37,45),(38,7),(38,12),(38,27),(38,33),(38,37),(38,52),(38,58),(38,65),(38,80),(38,86),(39,4),(39,11),(39,23),(39,35),(39,37),(39,49),(39,61),(39,66),(39,78),(39,90),(40,3),(40,13),(40,24),(40,32),(40,37),(40,48),(40,56),(40,70),(40,81),(40,89),(41,5),(41,17),(41,21),(41,31),(41,37),(41,50),(41,63),(41,69),(41,79),(41,83),(42,8),(42,18),(42,22),(42,29),(42,37),(42,53),(42,60),(42,68),(42,75),(42,88),(43,2),(43,16),(43,26),(43,36),(43,37),(43,47),(43,57),(43,67),(43,77),(43,87),(44,6),(44,14),(44,25),(44,30),(44,37),(44,51),(44,62),(44,72),(44,74),(44,85),(45,9),(45,15),(45,20),(45,34),(45,37)],
  [(45,54),(45,59),(45,71),(45,76),(45,84),(46,0),(46,73),(46,74),(46,75),(46,76),(46,77),(46,78),(46,79),(46,80),(46,81),(47,9),(47,12),(47,26),(47,31),(47,43),(47,51),(47,56),(47,68),(47,73),(47,90),(48,5),(48,11),(48,24),(48,34),(48,40),(48,53),(48,57),(48,72),(48,73),(48,86),(49,6),(49,13),(49,27),(49,29),(49,39),(49,50),(49,61),(49,71),(49,73),(49,87),(50,3),(50,17),(50,25),(50,36),(50,41),(50,49),(50,60),(50,65),(50,73),(50,84),(51,4),(51,18),(51,21),(51,33),(51,44),(51,47),(51,59),(51,70),(51,73),(51,85),(52,8),(52,16),(52,23),(52,30),(52,38),(52,54),(52,58),(52,69),(52,73),(52,89),(53,7),(53,14),(53,20),(53,35),(53,42),(53,48),(53,63),(53,67),(53,73),(53,88),(54,2),(54,15),(54,22),(54,32),(54,45),(54,52)],
  [(54,62),(54,66),(54,73),(54,83),(55,0),(55,82),(55,83),(55,84),(55,85),(55,86),(55,87),(55,88),(55,89),(55,90),(56,8),(56,12),(56,25),(56,32),(56,40),(56,47),(56,63),(56,71),(56,78),(56,82),(57,6),(57,11),(57,22),(57,36),(57,43),(57,48),(57,59),(57,69),(57,80),(57,82),(58,9),(58,13),(58,21),(58,35),(58,38),(58,52),(58,60),(58,72),(58,77),(58,82),(59,7),(59,17),(59,23),(59,29),(59,45),(59,51),(59,57),(59,70),(59,76),(59,82),(60,3),(60,18),(60,26),(60,34),(60,42),(60,50),(60,58),(60,66),(60,74),(60,82),(61,5),(61,16),(61,20),(61,33),(61,39),(61,49),(61,62),(61,68),(61,81),(61,82),(62,2),(62,14),(62,24),(62,31),(62,44),(62,54),(62,61),(62,65),(62,75),(62,82),(63,4),(63,15),(63,27),(63,30),(63,41),(63,53),(63,56)],
  [(63,67),(63,79),(63,82),(64,0),(64,64),(64,65),(64,66),(64,67),(64,68),(64,69),(64,70),(64,71),(64,72),(65,4),(65,12),(65,24),(65,36),(65,38),(65,50),(65,62),(65,64),(65,76),(65,88),(66,7),(66,11),(66,26),(66,32),(66,39),(66,54),(66,60),(66,64),(66,79),(66,85),(67,2),(67,13),(67,23),(67,33),(67,43),(67,53),(67,63),(67,64),(67,74),(67,84),(68,9),(68,17),(68,22),(68,30),(68,42),(68,47),(68,61),(68,64),(68,81),(68,86),(69,6),(69,18),(69,20),(69,31),(69,41),(69,52),(69,57),(69,64),(69,78),(69,89),(70,3),(70,16),(70,27),(70,35),(70,40),(70,51),(70,59),(70,64),(70,75),(70,83),(71,8),(71,14),(71,21),(71,34),(71,45),(71,49),(71,56),(71,64),(71,80),(71,87),(72,5),(72,15),(72,25),(72,29),(72,44),(72,48),(72,58),(72,64)],
  [(72,77),(72,90),(73,0),(73,46),(73,47),(73,48),(73,49),(73,50),(73,51),(73,52),(73,53),(73,54),(74,6),(74,12),(74,23),(74,34),(74,44),(74,46),(74,60),(74,67),(74,81),(74,83),(75,8),(75,11),(75,27),(75,31),(75,42),(75,46),(75,62),(75,70),(75,77),(75,84),(76,5),(76,13),(76,26),(76,30),(76,45),(76,46),(76,59),(76,65),(76,78),(76,88),(77,4),(77,17),(77,20),(77,32),(77,43),(77,46),(77,58),(77,72),(77,75),(77,87),(78,2),(78,18),(78,25),(78,35),(78,39),(78,46),(78,56),(78,69),(78,76),(78,86),(79,9),(79,16),(79,24),(79,29),(79,41),(79,46),(79,63),(79,66),(79,80),(79,85),(80,3),(80,14),(80,22),(80,33),(80,38),(80,46),(80,57),(80,71),(80,79),(80,90),(81,7),(81,15),(81,21),(81,36),(81,40),(81,46),(81,61),(81,68),(81,74)],
  [(81,89),(82,0),(82,55),(82,56),(82,57),(82,58),(82,59),(82,60),(82,61),(82,62),(82,63),(83,5),(83,12),(83,22),(83,35),(83,41),(83,54),(83,55),(83,70),(83,74),(83,87),(84,9),(84,11),(84,25),(84,33),(84,45),(84,50),(84,55),(84,67),(84,75),(84,89),(85,8),(85,13),(85,20),(85,36),(85,44),(85,51),(85,55),(85,66),(85,79),(85,86),(86,2),(86,17),(86,27),(86,34),(86,38),(86,48),(86,55),(86,68),(86,78),(86,85),(87,7),(87,18),(87,24),(87,30),(87,43),(87,49),(87,55),(87,71),(87,77),(87,83),(88,6),(88,16),(88,21),(88,32),(88,42),(88,53),(88,55),(88,65),(88,76),(88,90),(89,4),(89,14),(89,26),(89,29),(89,40),(89,52),(89,55),(89,69),(89,81),(89,84),(90,3),(90,15),(90,23),(90,31),(90,39),(90,47),(90,55),(90,72),(90,80),(90,88)]]
def incTab : List (ℕ × ℕ) := incTabs.flatten
def delNat : List ℕ := [7, 8, 9, 30, 31, 38, 39, 56, 57, 60, 68, 75, 79, 84, 88, 94, 102, 103, 117, 122, 127, 128, 141, 151, 154, 155, 157, 163, 164, 166, 167, 168, 176, 179, 183, 187, 203, 207, 208, 212, 215, 221, 224, 225, 231, 234, 236, 237, 238, 242, 243, 251, 253, 266, 282, 290, 300, 309, 318, 321, 324, 325, 330, 333, 338, 341, 349, 380, 386, 387, 389, 396, 398, 400, 401, 406, 407, 409, 411, 412, 418, 425, 426, 428, 439, 444, 454, 458, 464, 465, 468, 470, 476, 480, 481, 492, 502, 503, 504, 513, 517, 521, 522, 527, 539, 541, 544, 548, 552, 557, 559, 569, 579, 583, 585, 588, 592, 593, 598, 602, 603, 606, 607, 612, 619, 620, 632, 634, 643, 646, 670, 672, 673, 674, 682, 685, 688, 694, 695, 701, 702, 703, 709, 716, 718, 737, 746, 754, 757, 759, 773, 790, 821, 835, 837, 838, 839, 841, 842, 843, 846, 850, 853, 856, 857, 861, 862, 882, 884, 885, 887, 900, 901, 904, 907]

theorem mem_deleted (q : Edge) : q ∈ deleted ↔ q.val ∈ delNat := by
  simp only [deleted, delNat, Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
  rfl

theorem inc_eq : incidenceList.map (fun p => (p.1.val, p.2.val)) = incTab := by
  rw [MultipleUnicast.Counterexample.Dev.IncRows.incidenceList_map]; decide +kernel

theorem getD_flatten91 {α : Type} (L : List (List α)) (d : α) (hL : ∀ l ∈ L, l.length = 91) :
    ∀ (k m : ℕ), m < 91 → L.flatten.getD (91 * k + m) d = (L.getD k []).getD m d := by
  induction L with
  | nil => intro k m _; simp
  | cons l L ih =>
    intro k m hm
    have hl : l.length = 91 := hL l (by simp)
    rw [List.flatten_cons]
    cases k with
    | zero =>
      rw [List.getD_append _ _ _ _ (by omega)]; simp
    | succ k =>
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have : 91 * (k + 1) + m - l.length = 91 * k + m := by omega
      rw [this, ih (fun l' hl' => hL l' (by simp [hl'])) k m hm]
      simp

theorem incTabs_len : ∀ l ∈ incTabs, l.length = 91 := by decide +kernel

theorem split91 (n : ℕ) : n = 91 * (n / 91) + n % 91 := (Nat.div_add_mod n 91).symm

theorem edgePair_vals (q : Edge) :
    ((edgePair q).1.val, (edgePair q).2.val) = incTab.getD q.val (0,0) := by
  have h0 : ((0, 0) : ℕ × ℕ) = (fun p : Fin 91 × Fin 91 => (p.1.val, p.2.val)) (0, 0) := rfl
  rw [← inc_eq, h0, List.getD_map]
  rfl

theorem edgePair_fst (q : Edge) : ((edgePair q).1.val) = (incTab.getD q.val (0,0)).1 := by
  rw [← edgePair_vals]

theorem edgePair_snd (q : Edge) : ((edgePair q).2.val) = (incTab.getD q.val (0,0)).2 := by
  rw [← edgePair_vals]

def pe (n : ℕ) : ℕ := (incTab.getD n (0,0)).1
def le (n : ℕ) : ℕ := 91 + (incTab.getD n (0,0)).2

theorem pointEnd_val (q : Edge) : (pointEnd q).val = pe q.val := by
  simp only [pointEnd, pe, edgePair_fst]

theorem lineEnd_val (q : Edge) : (lineEnd q).val = le q.val := by
  simp only [lineEnd, le, edgePair_snd]


end MultipleUnicast.Counterexample.Dev.Bal
end

section
set_option maxRecDepth 4096
set_option autoImplicit false
set_option Elab.async false

namespace MultipleUnicast.Counterexample.Dev.TermDist
open MultipleUnicast.Counterexample MultipleUnicast.Counterexample.Dev.Bal Matrix

/-! ### Spanning-tree certificate: `parL v` is a physical edge joining `v` to `upL v`,
and `depL (upL v) < depL v`. -/
def parL : List ℕ := [0, 11, 21, 33, 41, 51, 61, 71, 81, 91, 101, 110, 120, 130, 140, 150, 160, 170, 180, 191, 201, 213, 223, 233, 240, 250, 263, 273, 281, 292, 302, 312, 322, 332, 342, 352, 362, 371, 384, 394, 404, 414, 424, 434, 440, 450, 460, 471, 486, 490, 509, 510, 520, 530, 549, 550, 560, 570, 580, 590, 605, 610, 628, 630, 640, 650, 660, 679, 680, 690, 708, 710, 720, 731, 745, 755, 765, 775, 785, 795, 805, 815, 820, 836, 840, 851, 866, 876, 886, 896, 906, 100, 0, 210, 20, 104, 105, 106, 107, 108, 109, 1, 121, 111, 131, 171, 181, 161, 18, 19, 2, 772, 112, 132, 172, 182, 162, 142, 152, 3, 123, 113, 133, 173, 53, 43, 143, 153, 4, 124, 114, 134, 174, 184, 24, 144, 344, 5, 125, 115, 135, 175, 185, 165, 145, 25, 6, 126, 116, 136, 76, 186, 336, 146, 156, 641, 47, 77, 137, 177, 67, 357, 147, 297, 461, 348, 118, 138, 178, 188, 98, 148, 158, 551, 129, 119, 139, 29, 189, 169, 149, 159]
def upL : List ℕ := [0, 101, 101, 121, 101, 101, 101, 101, 101, 101, 92, 92, 92, 92, 92, 92, 92, 92, 92, 119, 103, 119, 119, 119, 100, 98, 119, 119, 110, 110, 110, 110, 110, 110, 110, 110, 110, 128, 128, 128, 128, 128, 128, 128, 97, 100, 91, 103, 148, 97, 175, 95, 99, 98, 174, 91, 99, 97, 100, 98, 141, 96, 166, 95, 91, 95, 98, 175, 100, 97, 166, 99, 96, 137, 137, 137, 137, 137, 137, 137, 137, 137, 91, 146, 100, 104, 146, 146, 146, 146, 146, 10, 0, 21, 2, 10, 10, 10, 10, 10, 10, 0, 12, 11, 13, 17, 18, 16, 1, 1, 0, 77, 11, 13, 17, 18, 16, 14, 15, 0, 12, 11, 13, 17, 5, 4, 14, 15, 0, 12, 11, 13, 17, 18, 2, 14, 34, 0, 12, 11, 13, 17, 18, 16, 14, 2, 0, 12, 11, 13, 7, 18, 33, 14, 15, 64, 4, 7, 13, 17, 6, 35, 14, 29, 46, 34, 11, 13, 17, 18, 9, 14, 15, 55, 12, 11, 13, 2, 18, 16, 14, 15]
def depL : List ℕ := [0, 2, 2, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 2, 4, 4, 2, 2, 2, 2, 2, 3, 1, 3, 3, 3, 3, 3, 3, 3, 3, 1, 3, 3, 3, 3, 3, 3, 3, 3, 1, 3, 3, 3, 3, 3, 3, 3, 3, 1, 3, 3, 3, 3, 3, 3, 3, 3, 1, 3, 3, 3, 3, 3, 3, 3, 3, 1, 3, 3, 3, 3, 3, 3, 3, 3, 1, 3, 3, 3, 3, 3, 3, 3, 3, 5, 3, 3, 3, 3, 3, 3, 3, 3, 5, 3, 3, 3, 3, 3, 3, 3, 3, 5, 3, 3, 3, 3, 3, 3, 3, 3]

def peAt (n : ℕ) : ℕ := ((incTabs.getD (n / 91) []).getD (n % 91) (0,0)).1
def leAt (n : ℕ) : ℕ := 91 + ((incTabs.getD (n / 91) []).getD (n % 91) (0,0)).2

theorem pe_at (n : ℕ) : pe n = peAt n := by
  unfold pe peAt
  rw [incTab, split91 n, getD_flatten91 _ _ incTabs_len _ _ (Nat.mod_lt _ (by norm_num)), ← split91]

theorem le_at (n : ℕ) : le n = leAt n := by
  unfold le leAt
  rw [incTab, split91 n, getD_flatten91 _ _ incTabs_len _ _ (Nat.mod_lt _ (by norm_num)), ← split91]

def ok (v : ℕ) : Bool :=
  decide (parL.getD v 0 < 910) && decide (upL.getD v 0 < 182) &&
    !(delNat.contains (parL.getD v 0)) &&
    decide (depL.getD (upL.getD v 0) 0 < depL.getD v 0) &&
    ((peAt (parL.getD v 0) == v && leAt (parL.getD v 0) == upL.getD v 0) ||
      (peAt (parL.getD v 0) == upL.getD v 0 && leAt (parL.getD v 0) == v))

theorem cert0 : ∀ v : Fin 182, 0 ≤ v.val → v.val < 19 → v.val = 0 ∨ ok v.val = true := by
  decide +kernel
theorem cert1 : ∀ v : Fin 182, 19 ≤ v.val → v.val < 38 → v.val = 0 ∨ ok v.val = true := by
  decide +kernel
theorem cert2 : ∀ v : Fin 182, 38 ≤ v.val → v.val < 57 → v.val = 0 ∨ ok v.val = true := by
  decide +kernel
theorem cert3 : ∀ v : Fin 182, 57 ≤ v.val → v.val < 76 → v.val = 0 ∨ ok v.val = true := by
  decide +kernel
theorem cert4 : ∀ v : Fin 182, 76 ≤ v.val → v.val < 95 → v.val = 0 ∨ ok v.val = true := by
  decide +kernel
theorem cert5 : ∀ v : Fin 182, 95 ≤ v.val → v.val < 114 → v.val = 0 ∨ ok v.val = true := by
  decide +kernel
theorem cert6 : ∀ v : Fin 182, 114 ≤ v.val → v.val < 133 → v.val = 0 ∨ ok v.val = true := by
  decide +kernel
theorem cert7 : ∀ v : Fin 182, 133 ≤ v.val → v.val < 152 → v.val = 0 ∨ ok v.val = true := by
  decide +kernel
theorem cert8 : ∀ v : Fin 182, 152 ≤ v.val → v.val < 171 → v.val = 0 ∨ ok v.val = true := by
  decide +kernel
theorem cert9 : ∀ v : Fin 182, 171 ≤ v.val → v.val < 182 → v.val = 0 ∨ ok v.val = true := by
  decide +kernel
theorem cert (v : Fin 182) : v.val = 0 ∨ ok v.val = true := by
  have h := v.isLt
  by_cases h0 : v.val < 19; · exact cert0 v (by omega) h0
  by_cases h1 : v.val < 38; · exact cert1 v (by omega) h1
  by_cases h2 : v.val < 57; · exact cert2 v (by omega) h2
  by_cases h3 : v.val < 76; · exact cert3 v (by omega) h3
  by_cases h4 : v.val < 95; · exact cert4 v (by omega) h4
  by_cases h5 : v.val < 114; · exact cert5 v (by omega) h5
  by_cases h6 : v.val < 133; · exact cert6 v (by omega) h6
  by_cases h7 : v.val < 152; · exact cert7 v (by omega) h7
  by_cases h8 : v.val < 171; · exact cert8 v (by omega) h8
  exact cert9 v (by omega) (by omega)

theorem reach0 (v : Vertex) : graph.Reachable 0 v := by
  suffices h : ∀ n, ∀ v : Vertex, depL.getD v.val 0 = n → graph.Reachable 0 v from h _ v rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro v hv
  rcases cert v with h0 | h
  · have : v = 0 := Fin.ext h0
    subst this; rfl
  · simp only [ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.or_eq_true,
      beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hq, hu⟩, hd⟩, hdep⟩, hends⟩ := h
    let q : Edge := ⟨parL.getD v.val 0, hq⟩
    let u : Vertex := ⟨upL.getD v.val 0, hu⟩
    have hphys : q ∈ physical := by
      simp only [physical, Finset.mem_sdiff, Finset.mem_univ, true_and, mem_deleted]
      intro hm
      have h' : delNat.contains q.val = true := by simpa using hm
      exact Bool.false_ne_true (hd.symm.trans h')
    have hadj : graph.Adj u v := by
      refine ⟨q, hphys, ?_⟩
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; exact ⟨Fin.ext (by rw [lineEnd_val, le_at]; exact h2.symm),
          Fin.ext (by rw [pointEnd_val, pe_at]; exact h1.symm)⟩
      · left; exact ⟨Fin.ext (by rw [pointEnd_val, pe_at]; exact h1.symm),
          Fin.ext (by rw [lineEnd_val, le_at]; exact h2.symm)⟩
    exact (ih _ (hv ▸ hdep) u rfl).trans hadj.reachable

/-! ### Bipartiteness -/

theorem pe_lt (q : Edge) : (pointEnd q).val < 91 := (edgePair q).1.isLt
theorem le_ge (q : Edge) : 91 ≤ (lineEnd q).val := Nat.le_add_right _ _

theorem adj_side {u v : Vertex} (h : graph.Adj u v) : (u.val < 91 ↔ ¬ v.val < 91) := by
  obtain ⟨q, -, h⟩ := h
  have := pe_lt q
  have := le_ge q
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

theorem walk_parity {u v : Vertex} (w : graph.Walk u v) :
    ((u.val < 91 ↔ v.val < 91) ↔ Even w.length) := by
  induction w with
  | nil => simp
  | cons h w ih =>
    rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ← ih]
    have := adj_side h
    tauto

theorem adj_pl {u v : Vertex} (h : graph.Adj u v) (hu : u.val < 91) :
    ∃ q ∈ physical, u = pointEnd q ∧ v = lineEnd q := by
  obtain ⟨q, hq, h⟩ := h
  rcases h with h | ⟨h1, h2⟩
  · exact ⟨q, hq, h⟩
  · have := le_ge q
    rw [h1] at hu; omega

theorem adj_lp {u v : Vertex} (h : graph.Adj u v) (hu : 91 ≤ u.val) :
    ∃ q ∈ physical, u = lineEnd q ∧ v = pointEnd q := by
  obtain ⟨q, hq, h⟩ := h
  rcases h with ⟨h1, h2⟩ | h
  · have := pe_lt q
    rw [h1] at hu; omega
  · exact ⟨q, hq, h⟩

theorem not_del {q : Edge} (h : q ∈ physical) : q ∉ deleted := (Finset.mem_sdiff.1 h).2

theorem eq_of_ends {q e : Edge} (h1 : pointEnd q = pointEnd e) (h2 : lineEnd q = lineEnd e) :
    q = e := by
  apply balanced_orientation.2.2.1
  have a := congrArg Fin.val h1
  have b := congrArg Fin.val h2
  simp only [pointEnd, lineEnd] at a b
  exact Prod.ext (Fin.ext a) (Fin.ext (by omega))

theorem pt_idx {q e : Edge} (h : pointEnd q = pointEnd e) : (edgePair q).1 = (edgePair e).1 := by
  have a := congrArg Fin.val h
  simp only [pointEnd] at a
  exact Fin.ext a

theorem ln_idx {q e : Edge} (h : lineEnd q = lineEnd e) : (edgePair q).2 = (edgePair e).2 := by
  have b := congrArg Fin.val h
  simp only [lineEnd] at b
  exact Fin.ext (by omega)

/-! ### Every candidate edge is an incidence -/

theorem inc (q : Edge) : dot (triple (edgePair q).1) (triple (edgePair q).2) = 0 := by
  have hl := balanced_orientation.1
  have hlt : q.val < incidenceList.length := by omega
  have hm : edgePair q ∈ incidenceList := by
    unfold edgePair
    rw [List.getD_eq_getElem _ _ hlt]
    exact List.getElem_mem _
  unfold incidenceList at hm
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq] at hm
  obtain ⟨i, j, hj, hij⟩ := hm
  rw [← hij]
  exact hj

/-! ### Two distinct points lie on at most one common line -/

def Nrm (u : Triple) : Prop := (u 0 = 0 ∧ u 1 = 0 ∧ u 2 = 1) ∨ (u 0 = 0 ∧ u 1 = 1) ∨ u 0 = 1

theorem nrm_triple (i : Fin 91) : Nrm (triple i) := by
  unfold triple Nrm
  split_ifs <;> simp

theorem cross_zero_eq {u v : Triple} (hu : Nrm u) (hv : Nrm v) (h : u ⨯₃ v = 0) : u = v := by
  have h0 : u 1 * v 2 - u 2 * v 1 = 0 := congrFun h 0
  have h1 : u 2 * v 0 - u 0 * v 2 = 0 := congrFun h 1
  have h2 : u 0 * v 1 - u 1 * v 0 = 0 := congrFun h 2
  clear h
  have e : u 0 = v 0 ∧ u 1 = v 1 ∧ u 2 = v 2 := by
    rcases hu with ⟨a0, a1, a2⟩ | ⟨a0, a1⟩ | a0 <;>
    rcases hv with ⟨b0, b1, b2⟩ | ⟨b0, b1⟩ | b0 <;> grind
  funext k
  fin_cases k
  exacts [e.1, e.2.1, e.2.2]

def code (c : F9) : ℕ := c.re.val + 3 * c.im.val

def dec (u : Triple) : ℕ :=
  if code (u 0) = 0 then (if code (u 1) = 0 then 0 else 1 + code (u 2))
  else 10 + 9 * code (u 1) + code (u 2)

theorem dec_triple : ∀ i : Fin 91, dec (triple i) = i.val := by decide +kernel

theorem triple_inj : Function.Injective triple := fun i j h =>
  Fin.ext (by rw [← dec_triple i, ← dec_triple j, h])

theorem par {a b n : Triple} (ha : a ⨯₃ n = 0) (hb : b ⨯₃ n = 0) (hn : n ≠ 0) :
    a ⨯₃ b = 0 := by
  have a0 : a 1 * n 2 - a 2 * n 1 = 0 := congrFun ha 0
  have a1 : a 2 * n 0 - a 0 * n 2 = 0 := congrFun ha 1
  have a2 : a 0 * n 1 - a 1 * n 0 = 0 := congrFun ha 2
  have b0 : b 1 * n 2 - b 2 * n 1 = 0 := congrFun hb 0
  have b1 : b 2 * n 0 - b 0 * n 2 = 0 := congrFun hb 1
  have b2 : b 0 * n 1 - b 1 * n 0 = 0 := congrFun hb 2
  have hk : n 0 ≠ 0 ∨ n 1 ≠ 0 ∨ n 2 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hn (funext fun k => by fin_cases k <;> simp [hc.1, hc.2.1, hc.2.2])
  clear ha hb hn
  have e : a 1 * b 2 - a 2 * b 1 = 0 ∧ a 2 * b 0 - a 0 * b 2 = 0 ∧ a 0 * b 1 - a 1 * b 0 = 0 := by
    rcases hk with hk | hk | hk <;> refine ⟨?_, ?_, ?_⟩ <;> grind
  funext k
  fin_cases k
  exacts [e.1, e.2.1, e.2.2]

theorem plane {P1 P2 L1 L2 : Fin 91}
    (h11 : dot (triple P1) (triple L1) = 0) (h12 : dot (triple P1) (triple L2) = 0)
    (h21 : dot (triple P2) (triple L1) = 0) (h22 : dot (triple P2) (triple L2) = 0) :
    P1 = P2 ∨ L1 = L2 := by
  by_contra hc
  push Not at hc
  have hn : triple P1 ⨯₃ triple P2 ≠ 0 := fun h =>
    hc.1 (triple_inj (cross_zero_eq (nrm_triple _) (nrm_triple _) h))
  have key : ∀ L : Fin 91, dot (triple P1) (triple L) = 0 → dot (triple P2) (triple L) = 0 →
      triple L ⨯₃ (triple P1 ⨯₃ triple P2) = 0 := by
    intro L e1 e2
    change triple P1 ⬝ᵥ triple L = 0 at e1
    change triple P2 ⬝ᵥ triple L = 0 at e2
    rw [cross_cross_eq_smul_sub_smul', dotProduct_comm, e1, e2]
    simp
  exact hc.2 (triple_inj (cross_zero_eq (nrm_triple _) (nrm_triple _)
    (par (key L1 h11 h21) (key L2 h12 h22) hn)))

/-! ### No short walks between the ends of a deleted edge -/

theorem no_short (e : Edge) (he : e ∈ deleted) (w : graph.Walk (pointEnd e) (lineEnd e))
    (hw : w.length < 5) : False := by
  have hpar := walk_parity w
  have hp := pe_lt e
  have hl := le_ge e
  have hodd : ¬ Even w.length := fun h => by
    have := hpar.2 h
    omega
  have hcase : w.length = 1 ∨ w.length = 3 := by
    rcases Nat.even_or_odd w.length with h | ⟨m, hm⟩
    · exact absurd h hodd
    · omega
  have g0 := w.getVert_zero
  have gl := w.getVert_length
  rcases hcase with h1 | h3
  · have hadj := w.adj_getVert_succ (i := 0) (by omega)
    rw [g0, zero_add, ← h1, gl] at hadj
    obtain ⟨q, hq, e1, e2⟩ := adj_pl hadj hp
    exact not_del hq (eq_of_ends e1.symm e2.symm ▸ he)
  · have ad1 := w.adj_getVert_succ (i := 0) (by omega)
    have ad2 := w.adj_getVert_succ (i := 1) (by omega)
    have ad3 := w.adj_getVert_succ (i := 2) (by omega)
    rw [g0] at ad1
    rw [show 2 + 1 = w.length by omega, gl] at ad3
    simp only [Nat.reduceAdd] at ad1 ad2
    obtain ⟨q1, hq1, e11, e12⟩ := adj_pl ad1 hp
    rw [e12] at ad2
    obtain ⟨q2, hq2, e21, e22⟩ := adj_lp ad2 (le_ge q1)
    rw [e22] at ad3
    obtain ⟨q3, hq3, e31, e32⟩ := adj_pl ad3 (pe_lt q2)
    -- incidences: e = (P, L), q1 = (P, A), q2 = (B, A), q3 = (B, L)
    have i0 := inc e
    have i1 := inc q1
    have i2 := inc q2
    have i3 := inc q3
    rw [pt_idx e11.symm] at i1
    rw [ln_idx e21.symm] at i2
    rw [pt_idx e31.symm, ln_idx e32.symm] at i3
    rcases plane i0 i1 i3 i2 with hP | hL
    · -- q3 = e
      have : q3 = e := by
        refine eq_of_ends ?_ e32.symm
        have h1 := congrArg Fin.val hP
        have h2 := congrArg Fin.val e31
        apply Fin.ext
        simp only [pointEnd] at h1 h2 ⊢
        omega
      exact not_del hq3 (this ▸ he)
    · have : q1 = e := by
        refine eq_of_ends e11.symm ?_
        have := congrArg Fin.val hL
        apply Fin.ext
        simp only [lineEnd] at this ⊢
        omega
      exact not_del hq1 (this ▸ he)

theorem edge_main (e : Edge) (he : e ∈ deleted) :
    graph.Reachable (pointEnd e) (lineEnd e) ∧ 5 ≤ graph.dist (pointEnd e) (lineEnd e) := by
  have hr : graph.Reachable (pointEnd e) (lineEnd e) := (reach0 _).symm.trans (reach0 _)
  refine ⟨hr, ?_⟩
  by_contra hlt
  obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_dist
  exact no_short e he w (by omega)

end MultipleUnicast.Counterexample.Dev.TermDist

namespace MultipleUnicast.Counterexample

theorem chk_terminal_distance : ∀ i : Fin network.k,
    graph.Reachable (network.s i) (network.t i) ∧
    5 ≤ graph.dist (network.s i) (network.t i) := by
  intro i
  have he : (sessionEquiv i).val ∈ deleted := (Finset.mem_sdiff.1 (sessionEquiv i).2).1
  obtain ⟨h1, h2⟩ := Dev.TermDist.edge_main _ he
  show graph.Reachable (earlier _) (later _) ∧ 5 ≤ graph.dist (earlier _) (later _)
  unfold earlier later
  split_ifs
  · exact ⟨h1, h2⟩
  · exact ⟨h1.symm, by rw [SimpleGraph.dist_comm]; exact h2⟩


end MultipleUnicast.Counterexample
end

theorem solution : type_of% @MultipleUnicast.Counterexample.chk_terminal_distance := @MultipleUnicast.Counterexample.chk_terminal_distance
